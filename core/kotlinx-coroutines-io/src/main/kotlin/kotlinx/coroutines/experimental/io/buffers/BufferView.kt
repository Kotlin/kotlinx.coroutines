package kotlinx.coroutines.experimental.io.buffers

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.io.*
import kotlinx.coroutines.experimental.io.internal.*
import kotlinx.coroutines.experimental.io.packet.*

internal class BufferView private constructor(private var content: ByteBuffer,
                                                 private val origin: BufferView?,
                                                 private val pool: ObjectPool<BufferView>?) {

    constructor(pool: ObjectPool<ByteBuffer>) : this(pool.borrow(), null, null)
    constructor(buffer: ByteBuffer, pool: ObjectPool<BufferView>) : this(buffer, null, pool)
    constructor(buffer: ByteBuffer) : this(buffer, null, null)

    private var duplicated: ByteBuffer? = null

    private var limit = content.limit()
    private var readPosition = 0
    private var writePosition = 0
    private val refCount = atomic(1L)

    var next: BufferView? = null
        set(newValue) {
            if (newValue === this) throw IllegalArgumentException("next == this")
            field = newValue
        }
    var attachment: Any? = null

    var order: ByteOrder = ByteOrder.BIG_ENDIAN
        set(value) {
            content.order(value)
            field = value
        }

    inline val readRemaining: Int get() = writePosition - readPosition
    inline val writeRemaining: Int get() = limit - writePosition

    val startGap: Int get() = readPosition
    val endGap: Int get() = limit - writePosition

    fun hasRemaining() = writePosition > readPosition

    init {
        content.order(order)
    }

    operator fun get(index: Int) = content.get(index)
    operator fun set(index: Int, value: Byte) {
        content.put(index, value)
    }

    fun readByte(): Byte = read(1) { content.get(it) }
    fun readShort(): Short = read(2) { content.getShort(it) }
    fun readInt(): Int  = read(4) { content.getInt(it) }
    fun readLong(): Long = read(8) { content.getLong(it) }
    fun readFloat(): Float = read(4) { content.getFloat(it) }
    fun readDouble() = read(8) { content.getDouble(it) }

    fun discardExact(n: Int): Boolean {
        val newPosition = readPosition + n
        val delta = writePosition - newPosition

        if (delta < 0) {
            throw IllegalArgumentException("Unable to discard $n bytes: only $readRemaining available")
        } else if (n < 0) {
            throw IllegalArgumentException("Discarding negative amount of bytes: $n")
        }

        readPosition = newPosition
        return delta == 0
    }

    fun read(dst: ByteBuffer, size: Int): Int {
        require(size <= dst.remaining())

        val dup = readDuplicated(size)
        val actualSize = dup.remaining()
        dst.put(dup)
        readPosition += actualSize
        return actualSize
    }

    fun read(dst: ByteArray, offset: Int, length: Int) {
        val rp = readPosition
        require(writePosition - rp >= length) { throw IndexOutOfBoundsException("length > $readRemaining") }
        require(offset >= 0)
        require(offset < dst.size)
        require(offset + length <= dst.size)

        val dup = readDuplicated()
        dup.get(dst, offset, length)
        readPosition = rp + length
    }

    private inline fun <R> read(n: Int, block: (Int) -> R): R {
        val rp = readPosition

        require(n >= 0)
        require(n <= writePosition - rp)

        val r = block(rp)
        readPosition = rp + n

        return r
    }

    // write ops

    fun reserveStartGap(n: Int) {
        require(n >= 0)
        require(n <= limit)
        val rp = readPosition
        if (rp != 0) throw IllegalStateException("Can't reserve $n bytes gap: there is already a reserved gap ($rp bytes)")
        val wp = writePosition
        if (wp != 0 || rp != wp) throw IllegalStateException("Can't reserve $n bytes gap: there are already bytes written at the beginning")

        readPosition = rp + n
        writePosition = wp + n
    }

    fun reserveEndGap(n: Int) {
        require(n >= 0)
        require(n <= limit - writePosition)
        val actualLimit = content.limit()

        if (limit != actualLimit) throw IllegalStateException("Can't reserve $n bytes gap: there is already a reserved gap (${actualLimit - limit} bytes)")
        val newLimit = actualLimit - n

        if (newLimit < writePosition) throw IllegalStateException("Can't reserve $n bytes gap: there are already bytes written at the end - not enough space to reserve")

        limit = newLimit
    }

    fun writeByte(v: Byte) {
        content.put(writePosition, v)
        writePosition++
    }

    fun writeShort(v: Short) {
        content.putShort(writePosition, v)
        writePosition += 2
    }

    fun writeInt(v: Int) {
        content.putInt(writePosition, v)
        writePosition += 4
    }

    fun writeLong(v: Long) {
        content.putLong(writePosition, v)
        writePosition += 8
    }

    fun writeFloat(v: Float) {
        content.putFloat(writePosition, v)
        writePosition += 4
    }

    fun writeDouble(v: Double) {
        content.putDouble(writePosition, v)
        writePosition += 8
    }

    fun write(array: ByteArray, offset: Int, length: Int) {
        if (length == 0) return
        val buffer = writeDuplicated(length)
        buffer.put(array, offset, length)
        writePosition += length
    }

    fun write(bb: ByteBuffer) {
        val size = bb.remaining()
        if (size == 0) return

        val buffer = writeDuplicated(size)
        buffer.put(bb)
        writePosition += size
    }

    fun writeBuffer(other: BufferView, limit: Int = Int.MAX_VALUE): Int {
        val otherSize = other.limit- other.readPosition
        val mySize = limit - writePosition
        val size = minOf(limit, otherSize, mySize)

        val myBuffer = writeDuplicated(size)
        val otherBuffer = other.readDuplicated(size)

        myBuffer.put(otherBuffer)
        writePosition += size
        other.readPosition += size

        return size
    }

    fun writeBufferPrepend(other: BufferView) {
        val size = other.readRemaining
        val rp = readPosition

        if (size > rp) throw IllegalArgumentException("Can't prepend buffer: not enough free space in the beginning")

        val to = duplicated()
        to.limit(rp)
        to.position(rp - size)
        val from = other.readDuplicated()

        to.put(from)
        readPosition = rp - size
        other.readPosition += size
    }

    /**
     * Could write over the end gap!
     */
    fun writeBufferAppend(other: BufferView, maxSize: Int = Int.MAX_VALUE) {
        val size = minOf(other.readRemaining, maxSize)
        val wp = writePosition
        val actualLimit = content.limit()

        if (wp + size > actualLimit) throw IllegalArgumentException("Can't append buffer: not enough free space in the end")

        val to = writeDuplicated(size)
        val from = other.readDuplicated(size)

        to.put(from)
        writePosition += size
        limit = maxOf(limit, writePosition)
        other.readPosition += size
    }

    //

    fun pushBack(n: Int = 1) {
        val rp = readPosition
        val newRp = rp - n
        if (newRp < 0) throw IllegalStateException("Nothing to push back")
        readPosition = newRp
    }

    fun resetForWrite() {
        readPosition = 0
        writePosition = 0
    }

    fun resetForRead() {
        readPosition = 0
        writePosition = limit
    }

    fun isExclusivelyOwned(): Boolean = refCount.value == 1L

    fun makeView(): BufferView {
        (origin ?: this).acquire()

        val view = BufferView(content, origin, null)
        view.attachment = attachment
        view.readPosition = readPosition
        view.writePosition = writePosition
        view.limit = limit

        return view
    }

    fun release() {
        if (releaseRefCount()) {
            resetForWrite()

            if (origin != null) {
                unlink()
                origin.release()
            } else {
                pool?.recycle(this) ?: unlink()
            }
        }
    }

    internal inline fun readDirect(block: (ByteBuffer) -> Unit) {
        val bb = readDuplicated(readRemaining)
        val positionBefore = bb.position()
        val limit = bb.limit()
        block(bb)
        val delta = bb.position() - positionBefore
        if (delta < 0) throw IllegalStateException("Wrong buffer position change: negative shift $delta")
        if (bb.limit() != limit) throw IllegalStateException("Limit change is now allowed")

        readPosition += delta
    }

    internal inline fun writeDirect(size: Int, block: (ByteBuffer) -> Unit) {
        val rem = writeRemaining
        require (size <= rem) { "size $size is greater than buffer's remaining capacity $rem" }
        val buffer = writeDuplicated(rem)
        val positionBefore = buffer.position()
        block(buffer)
        val delta = buffer.position() - positionBefore
        if (delta < 0 || delta > rem) throw IllegalStateException("Wrong buffer position change: $delta (position should be moved forward only by at most size bytes (size =  $size)")

        writePosition += delta
    }

    private fun readDuplicated(limit: Int = Int.MAX_VALUE): ByteBuffer {
        val position = readPosition
        val upLimit = (position.toLong() + limit).coerceAtMost(Int.MAX_VALUE.toLong()).toInt()

        val buffer = duplicated()
        buffer.limit(minOf(writePosition, upLimit))
        buffer.position(position)
        return buffer
    }

    private fun writeDuplicated(limit: Int = Int.MAX_VALUE): ByteBuffer {
        val position = writePosition
        val upLimit = (position.toLong() + limit).coerceAtMost(Int.MAX_VALUE.toLong()).toInt()

        val buffer = duplicated()
        buffer.limit(minOf(this.limit, upLimit))
        buffer.position(position)
        return buffer
    }

    private fun duplicated(): ByteBuffer {
        return duplicated ?: content.duplicate()!!.also { duplicated = it }
    }

    private fun unlink(): ByteBuffer? {
        val empty = EmptyBuffer
        val buffer = content

        if (buffer === empty) return null

        content = empty
        duplicated = null

        return buffer
    }

    private fun releaseRefCount(): Boolean {
        return refCount.updateAndGet {
            if (it == 0L) throw IllegalStateException("Unable to release: already released")
            it - 1L
        } == 0L
    }

    private fun acquire() {
        refCount.update {
            if (it == 0L) throw IllegalStateException("Unable to acquire: already released")
            it + 1L
        }
    }

    internal object Pool : ObjectPoolImpl<BufferView>(PACKET_BUFFER_POOL_SIZE) {
        override fun produceInstance() = BufferView(ByteBuffer.allocateDirect(PACKET_BUFFER_SIZE), this)
        override fun clearInstance(instance: BufferView): BufferView {
            return instance.apply {
                next = null
                attachment = null
                content.clear()
                limit = content.limit()
                if (!refCount.compareAndSet(0L, 1L)) {
                    throw IllegalStateException("Unable to prepare buffer: refCount is not zero (used while parked in the pool?)")
                }
            }
        }

        override fun validateInstance(instance: BufferView) {
            require(instance.refCount.value == 0L) { "Buffer is not yet released but tried to recycle" }
            require(instance.origin == null) { "Unable to recycle buffer view, only origin buffers are applicable" }
        }
    }

    companion object {
        private val EmptyBuffer = ByteBuffer.allocate(0)!!

        val Empty = BufferView(EmptyBuffer)
    }
}