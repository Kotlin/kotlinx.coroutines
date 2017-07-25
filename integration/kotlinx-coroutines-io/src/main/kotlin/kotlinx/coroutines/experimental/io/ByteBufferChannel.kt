package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.io.internal.*
import java.nio.*
import java.nio.charset.*
import java.util.concurrent.atomic.*

open class ByteBufferChannel internal constructor(override val autoFlush: Boolean, val pool: ObjectPool<ReadWriteBufferState.Initial>) : ByteReadChannel, ByteWriteChannel {
    constructor(autoFlush: Boolean = false) : this(autoFlush, DirectBufferObjectPool)

    @Volatile
    protected var state: ReadWriteBufferState = ReadWriteBufferState.IdleEmpty

    @Volatile
    protected var closed: ClosedElement? = null

    @Volatile
    protected var readOp: ReadElement? = null

    @Volatile
    protected var writeOp: WriteElement? = null

    private var readPosition = 0
    private var writePosition = 0

    override var readByteOrder: ByteOrder = ByteOrder.BIG_ENDIAN
    override var writeByteOrder: ByteOrder = ByteOrder.BIG_ENDIAN

    override val remaining: Int
        get() = state.capacity.remaining

    override val isClosedForReceive: Boolean
        get() = state === ReadWriteBufferState.Terminated

    override fun close(cause: Throwable?): Boolean {
        if (closed != null) return false

        val newClosed = if (cause == null) ClosedElement.EmptyCause else ClosedElement(cause)
        if (!ClosedOp.compareAndSet(this, null, newClosed)) return false
        flush()

        if (state.capacity.isEmpty()) {
            tryTerminate()
        }

        resumeClosed(cause)

        return true
    }

    override fun flush() {
        if (state.capacity.flush()) {
            ReadOp.getAndSet(this, null)?.resume(true)
            if (state.capacity.capacity > 0) {
                resumeWriteOp()
            }
        }
    }

    private fun ByteBuffer.prepareBuffer(order: ByteOrder, position: Int, available: Int) {
        require(position >= 0)
        require(available >= 0)

        val bufferLimit = capacity() - ReservedSize
        val virtualLimit = position + available

        order(order.forNio)
        limit(virtualLimit.coerceAtMost(bufferLimit))
        position(position)
    }

    private fun setupStateForWrite(): ByteBuffer {
        var _allocated: ReadWriteBufferState.Initial? = null

        val (old, newState) = updateState { state ->
            when (state) {
                ReadWriteBufferState.IdleEmpty -> {
                    val allocated = _allocated ?: newBuffer().also { _allocated = it }
                    allocated.startWriting()
                }
                ReadWriteBufferState.Terminated -> throw closed!!.sendException
                else -> {
                    state.startWriting()
                }
            }
        }

        val buffer = newState.writeBuffer

        _allocated?.let { allocated ->
            if (old !== ReadWriteBufferState.IdleEmpty) {
                releaseBuffer(allocated)
            }
        }

        return buffer.apply {
            prepareBuffer(writeByteOrder, writePosition, newState.capacity.capacity)
        }
    }

    private fun restoreStateAfterWrite() {
        var toRelease: ReadWriteBufferState.IdleNonEmpty? = null

        val (_, newState) = updateState {
            val writeStopped = it.stopWriting()
            if (writeStopped is ReadWriteBufferState.IdleNonEmpty && writeStopped.capacity.isEmpty()) {
                toRelease = writeStopped
                ReadWriteBufferState.IdleEmpty
            } else {
                writeStopped
            }
        }

        if (newState === ReadWriteBufferState.IdleEmpty) {
            toRelease?.let { releaseBuffer(it.initial) }
        }
    }

    private fun setupStateForRead(): ByteBuffer? {
        val (_, newState) = updateState { state ->
            when (state) {
                ReadWriteBufferState.Terminated -> closed!!.cause?.let { throw it } ?: return null
                ReadWriteBufferState.IdleEmpty -> closed?.cause?.let { throw it } ?: return null
                else -> {
                    if (state.capacity.remaining == 0) return null
                    state.startReading()
                }
            }
        }

        return newState.readBuffer.apply {
            prepareBuffer(readByteOrder, readPosition, newState.capacity.remaining)
        }
    }

    private fun restoreStateAfterRead() {
        var toRelease: ReadWriteBufferState.IdleNonEmpty? = null

        val (_, newState) = updateState { state ->
            toRelease?.let {
                it.capacity.reset()
                resumeWriteOp()
                toRelease = null
            }

            val readStopped = state.stopReading()

            if (readStopped is ReadWriteBufferState.IdleNonEmpty) {
                if (this.state === state && readStopped.capacity.tryLockForRelease()) {
                    toRelease = readStopped
                    ReadWriteBufferState.IdleEmpty
                } else {
                    readStopped
                }
            } else {
                readStopped
            }
        }

        if (newState === ReadWriteBufferState.IdleEmpty) {
            toRelease?.let { releaseBuffer(it.initial) }
            resumeWriteOp()
        }
    }

    private fun tryTerminate() {
        if (closed != null) {
            updateState { state ->
                when {
                    state === ReadWriteBufferState.IdleEmpty -> ReadWriteBufferState.Terminated
                    else -> return
                }
            }

            WriteOp.getAndSet(this, null)?.resumeWithException(closed!!.sendException)
            ReadOp.getAndSet(this, null)?.apply {
                if (closed?.cause != null) resumeWithException(closed!!.cause!!) else resume(false)
            }
        }
    }

    private fun ByteBuffer.carryIndex(idx: Int) = if (idx >= capacity() - ReservedSize) idx - (capacity() - ReservedSize) else idx

    private inline fun writing(block: ByteBuffer.(RingBufferCapacity) -> Unit) {
        val buffer = setupStateForWrite()
        val capacity = state.capacity

        try {
            closed?.sendException?.let { throw it }
            block(buffer, capacity)
        } finally {
            if (capacity.isFull() || autoFlush) {
                flush()
            }

            restoreStateAfterWrite()
            tryTerminate()
        }
    }

    private inline fun reading(block: ByteBuffer.(RingBufferCapacity) -> Boolean): Boolean {
        val buffer = setupStateForRead() ?: return false
        val capacity = state.capacity

        try {
            if (capacity.remaining == 0) return false

            return block(buffer, capacity)
        } finally {
            restoreStateAfterRead()
            tryTerminate()
        }
    }

    override val isClosedForSend: Boolean
        get() = closed != null

    private fun readAsMuchAsPossible(dst: ByteBuffer, consumed0: Int = 0): Int {
        var consumed = 0

        val rc = reading {
            val part = it.tryReadAtMost(minOf(remaining(), dst.remaining()))
            if (part > 0) {
                consumed += part

                if (dst.remaining() >= remaining()) {
                    dst.put(this)
                } else {
                    repeat(part) {
                        dst.put(get())
                    }
                }

                readPosition = carryIndex(readPosition + part)

                it.completeRead(part)
                resumeWriteOp()
                true
            } else {
                false
            }
        }

        return if (rc && dst.hasRemaining() && state.capacity.remaining > 0)
            readAsMuchAsPossible(dst, consumed0 + consumed)
        else consumed + consumed0
    }

    private fun readAsMuchAsPossible(dst: ByteArray, offset: Int, length: Int, consumed0: Int = 0): Int {
        var consumed = 0

        val rc = reading {
            val part = it.tryReadAtMost(minOf(remaining(), length))
            if (part > 0) {
                consumed += part
                get(dst, offset, part)
                readPosition = carryIndex(readPosition + part)

                it.completeRead(part)
                resumeWriteOp()
                true
            } else {
                false
            }
        }

        return if (rc && consumed < length && state.capacity.remaining > 0)
            readAsMuchAsPossible(dst, offset + consumed, length - consumed, consumed0 + consumed)
        else consumed + consumed0
    }

    suspend override fun readFully(dst: ByteArray, offset: Int, length: Int) {
        val consumed = readAsMuchAsPossible(dst, offset, length)

        if (consumed < length) {
            readFullySuspend(dst, offset + consumed, length - consumed)
        }
    }

    suspend override fun readFully(dst: ByteBuffer) {
        readAsMuchAsPossible(dst)
        if (!dst.hasRemaining()) return

        return readFullySuspend(dst)
    }

    private suspend fun readFullySuspend(dst: ByteBuffer) {
        while (dst.hasRemaining()) {
            if (!readSuspend(1)) throw ClosedReceiveChannelException("Unexpected EOF: expected ${dst.remaining()} more bytes")
            readAsMuchAsPossible(dst)
        }
    }

    private suspend tailrec fun readFullySuspend(dst: ByteArray, offset: Int, length: Int) {
        if (!readSuspend(1)) throw ClosedReceiveChannelException("Unexpected EOF: expected $length more bytes")

        val consumed = readAsMuchAsPossible(dst, offset, length)

        if (consumed < length) {
            readFullySuspend(dst, offset + consumed, length - consumed)
        }
    }

    suspend override fun readLazy(dst: ByteArray, offset: Int, length: Int): Int {
        val consumed = readAsMuchAsPossible(dst, offset, length)

        return if (consumed > 0) consumed
        else readLazySuspend(dst, offset, length)
    }

    suspend override fun readLazy(dst: ByteBuffer): Int {
        val consumed = readAsMuchAsPossible(dst)
        if (consumed > 0) return consumed

        return readLazySuspend(dst)
    }

    private suspend fun readLazySuspend(dst: ByteArray, offset: Int, length: Int): Int {
        if (!readSuspend(1)) return -1
        return readLazy(dst, offset, length)
    }

    private suspend fun readLazySuspend(dst: ByteBuffer): Int {
        if (!readSuspend(1)) return -1
        return readLazy(dst)
    }

    suspend override fun readByte(): Byte {
        var b: Byte = 0

        val rc = reading {
            if (it.tryReadExact(1)) {
                b = get()
                readPosition = carryIndex(readPosition + 1)
                it.completeRead(1)
                resumeWriteOp()
                true
            } else false
        }

        return if (rc) {
            b
        } else {
            readByteSuspend()
        }
    }

    private suspend fun readByteSuspend(): Byte {
        if (!readSuspend(1)) throw ClosedReceiveChannelException("EOF: one byte required")
        return readByte()
    }

    suspend override fun readBoolean(): Boolean {
        var b = false

        val rc = reading {
            if (it.tryReadExact(1)) {
                b = get() != 0.toByte()
                readPosition = carryIndex(readPosition + 1)
                it.completeRead(1)
                resumeWriteOp()
                true
            } else false
        }

        return if (rc) {
            b
        } else {
            readBooleanSuspend()
        }
    }

    private suspend fun readBooleanSuspend(): Boolean {
        if (!readSuspend(1)) throw ClosedReceiveChannelException("EOF: one byte required")
        return readBoolean()
    }

    suspend override fun readUByte(): Short {
        TODO()
    }

    suspend override fun readShort(): Short {
        var sh: Short = 0

        val rc = reading {
            if (it.tryReadExact(2)) {
                if (remaining() < 2) rollBytes(2)
                sh = getShort()
                readPosition = carryIndex(readPosition + 2)
                it.completeRead(2)
                resumeWriteOp()
                true
            } else false
        }

        return if (rc) {
            sh
        } else {
            readShortSuspend()
        }
    }

    private suspend fun readShortSuspend(): Short {
        if (!readSuspend(2)) throw ClosedReceiveChannelException("EOF while byte expected")
        return readShort()
    }

    suspend override fun readUShort(): Int {
        TODO()
    }

    suspend override fun readInt(): Int {
        var i = 0

        val rc = reading {
            if (it.tryReadExact(4)) {
                if (remaining() < 4) rollBytes(4)
                i = getInt()
                readPosition = carryIndex(readPosition + 4)
                it.completeRead(4)
                resumeWriteOp()
                true
            } else false
        }

        return if (rc) {
            i
        } else {
            readIntSuspend()
        }
    }

    private fun ByteBuffer.rollBytes(n: Int) {
        limit(position() + n)
        for (i in 1..n - remaining()) {
            put(capacity() + ReservedLongIndex + i, get(i))
        }
    }

    private suspend fun readIntSuspend(): Int {
        if (!readSuspend(4)) throw ClosedReceiveChannelException("EOF while an int expected")
        return readInt()
    }

    suspend override fun readUInt(): Long {
        TODO()
    }

    suspend override fun readLong(): Long {
        var i = 0L

        val rc = reading {
            if (it.tryReadExact(8)) {
                if (remaining() < 8) rollBytes(8)
                i = getLong()
                readPosition = carryIndex(readPosition + 8)
                it.completeRead(8)
                resumeWriteOp()
                true
            } else false
        }

        return if (rc) {
            i
        } else {
            readLongSuspend()
        }
    }

    private suspend fun readLongSuspend(): Long {
        if (!readSuspend(8)) throw ClosedReceiveChannelException("EOF while a long expected")
        return readLong()
    }

    suspend override fun readDouble(): Double {
        var d = 0.0

        val rc = reading {
            if (it.tryReadExact(8)) {
                if (remaining() < 8) rollBytes(8)
                d = getDouble()
                readPosition = carryIndex(readPosition + 8)
                it.completeRead(8)
                resumeWriteOp()
                true
            } else false
        }

        return if (rc) {
            d
        } else {
            readDoubleSuspend()
        }
    }

    private suspend fun readDoubleSuspend(): Double {
        if (!readSuspend(8)) throw ClosedReceiveChannelException("EOF while a double expected")
        return readDouble()
    }

    suspend override fun readFloat(): Float {
        var f = 0.0f

        val rc = reading {
            if (it.tryReadExact(4)) {
                if (remaining() < 4) rollBytes(4)
                f = getFloat()
                readPosition = carryIndex(readPosition + 4)
                it.completeRead(4)
                resumeWriteOp()
                true
            } else false
        }

        return if (rc) {
            f
        } else {
            readFloatSuspend()
        }
    }

    private suspend fun readFloatSuspend(): Float {
        if (!readSuspend(4)) throw ClosedReceiveChannelException("EOF while an int expected")
        return readFloat()
    }

    private fun ByteBuffer.carry() {
        val base = capacity() - ReservedSize
        for (i in base until position()) {
            put(i - base, get(i))
        }
    }

    private fun ByteBuffer.bytesWritten(c: RingBufferCapacity, n: Int) {
        require(n >= 0)

        writePosition = carryIndex(writePosition + n)
        c.completeWrite(n)
    }

    suspend override fun writeByte(b: Byte) {
        writing {
            tryWriteByte(b, it)
        }
    }

    private suspend fun ByteBuffer.tryWriteByte(b: Byte, c: RingBufferCapacity) {
        if (c.tryWriteExact(1)) {
            put(b)
            bytesWritten(c, 1)
        } else {
            writeByteSuspend(b, c)
        }
    }

    private suspend fun ByteBuffer.writeByteSuspend(b: Byte, c: RingBufferCapacity) {
        writeSuspend(1)
        tryWriteByte(b, c)
    }

    suspend override fun writeShort(s: Short) {
        writing {
            if (!tryWriteShort(s, it)) {
                writeShortSuspend(s, it)
            }
        }
    }

    private suspend fun ByteBuffer.writeShortSuspend(s: Short, c: RingBufferCapacity) {
        writeSuspend(2)
        tryWriteShort(s, c)
    }

    private fun ByteBuffer.tryWriteShort(s: Short, c: RingBufferCapacity): Boolean {
        if (c.tryWriteExact(2)) {
            if (remaining() < 2) {
                limit(capacity())
                putShort(s)
                carry()
            } else {
                putShort(s)
            }

            bytesWritten(c, 2)
            return true
        }

        return false
    }

    private fun ByteBuffer.tryWriteInt(i: Int, c: RingBufferCapacity): Boolean {
        if (c.tryWriteExact(4)) {
            if (remaining() < 4) {
                limit(capacity())
                putInt(i)
                carry()
            } else {
                putInt(i)
            }

            bytesWritten(c, 4)
            return true
        }

        return false
    }

    suspend override fun writeInt(i: Int) {
        writing {
            if (!tryWriteInt(i, it)) {
                writeIntSuspend(i, it)
            }
        }
    }

    private suspend fun ByteBuffer.writeIntSuspend(i: Int, c: RingBufferCapacity) {
        writeSuspend(4)
        tryWriteInt(i, c)
    }

    private fun ByteBuffer.tryWriteLong(l: Long, c: RingBufferCapacity): Boolean {
        if (c.tryWriteExact(8)) {
            if (remaining() < 8) {
                limit(capacity())
                putLong(l)
                carry()
            } else {
                putLong(l)
            }

            bytesWritten(c, 8)
            return true
        }

        return false
    }

    suspend override fun writeLong(l: Long) {
        writing {
            if (!tryWriteLong(l, it)) {
                writeLongSuspend(l, it)
            }
        }
    }

    private suspend fun ByteBuffer.writeLongSuspend(l: Long, c: RingBufferCapacity) {
        writeSuspend(8)
        tryWriteLong(l, c)
    }

    suspend override fun writeDouble(d: Double) {
        writeLong(java.lang.Double.doubleToRawLongBits(d))
    }

    suspend override fun writeFloat(f: Float) {
        writeInt(java.lang.Float.floatToRawIntBits(f))
    }

    suspend override fun writeLazy(src: ByteBuffer): Int {
        val copied = writeAsMuchAsPossible(src)
        if (copied > 0) return copied

        return writeLazySuspend(src)
    }

    private suspend fun writeLazySuspend(src: ByteBuffer): Int {
        while (true) {
            writeSuspend(1)
            val copied = writeLazy(src)
            if (copied > 0) return copied
        }
    }

    suspend override fun writeFully(src: ByteBuffer) {
        writeAsMuchAsPossible(src)
        if (!src.hasRemaining()) return

        return writeFullySuspend(src)
    }

    private suspend fun writeFullySuspend(src: ByteBuffer) {
        while (src.hasRemaining()) {
            writeSuspend(1)
            writeAsMuchAsPossible(src)
        }
    }

    private fun writeAsMuchAsPossible(src: ByteBuffer): Int {
        writing {
            var written = 0

            do {
                val possibleSize = it.tryWriteAtMost(minOf(src.remaining(), remaining()))
                if (possibleSize == 0) break
                require(possibleSize > 0)

                if (remaining() >= src.remaining()) {
                    put(src)
                } else {
                    repeat(possibleSize) {
                        put(src.get())
                    }
                }

                written += possibleSize

                prepareBuffer(writeByteOrder, carryIndex(writePosition + written), it.capacity)
            } while (true)

            bytesWritten(it, written)

            return written
        }

        return 0
    }

    private fun writeAsMuchAsPossible(src: ByteArray, offset: Int, length: Int): Int {
        writing {
            var written = 0

            do {
                val possibleSize = it.tryWriteAtMost(minOf(length - written, remaining()))
                if (possibleSize == 0) break
                require(possibleSize > 0)

                put(src, offset + written, possibleSize)
                written += possibleSize

                prepareBuffer(writeByteOrder, carryIndex(writePosition + written), it.capacity)
            } while (true)

            bytesWritten(it, written)

            return written
        }

        return 0
    }

    suspend override fun writeFully(src: ByteArray, offset: Int, length: Int) {
        var rem = length
        var off = offset

        while (rem > 0) {
            val s = writeAsMuchAsPossible(src, off, rem)
            if (s == 0) break

            off += s
            rem -= s
        }

        if (rem == 0) return

        writeFullySuspend(src, off, rem)
    }

    private tailrec suspend fun writeFullySuspend(src: ByteArray, offset: Int, length: Int) {
        if (length == 0) return
        val copied = writeLazy(src, offset, length)
        return writeFullySuspend(src, offset + copied, length - copied)
    }

    suspend override fun writeLazy(src: ByteArray, offset: Int, length: Int): Int {
        val size = writeAsMuchAsPossible(src, offset, length)
        if (size > 0) return size
        return writeSuspend(src, offset, length)
    }

    private suspend fun writeSuspend(src: ByteArray, offset: Int, length: Int): Int {
        while (true) {
            writeSuspend(1)
            val size = writeAsMuchAsPossible(src, offset, length)
            if (size > 0) return size
        }
    }

    /**
     * Invokes [visitor] for every available batch until all bytes processed or visitor if visitor returns false.
     * Never invokes [visitor] with empty buffer unless [last] = true. Invokes visitor with last = true at most once
     * even if there are remaining bytes and visitor returned true.
     */
    override suspend fun lookAhead(visitor: (buffer: ByteBuffer, last: Boolean) -> Boolean) {
        if (lookAheadFast(false, visitor)) return
        lookAheadSuspend(visitor)
    }

    private inline fun lookAheadFast(last0: Boolean, visitor: (buffer: ByteBuffer, last: Boolean) -> Boolean): Boolean {
        if (state === ReadWriteBufferState.Terminated && !last0) return false

        val rc = reading {
            val last = last0

            do {
                val available = state.capacity.remaining

                val rem = if (available > 0 || last) {
                    if (!visitor(this, last)) {
                        afterBufferVisited(this, it)
                        return true
                    }

                    val consumed = afterBufferVisited(this, it)
                    available - consumed
                } else 0
            } while (rem > 0 && !last)

            last
        }

        if (!rc && closed != null) {
            visitor(ReadWriteBufferState.Empty, true)
        }

        return rc
    }

    private suspend fun lookAheadSuspend(visitor: (buffer: ByteBuffer, last: Boolean) -> Boolean): Boolean {
        var last = false

        do {
            if (lookAheadFast(last, visitor)) return true
            if (last) return false
            if (!readSuspend(1)) {
                last = true
            }
        } while (true)
    }

    private fun afterBufferVisited(buffer: ByteBuffer, c: RingBufferCapacity): Int {
        val consumed = buffer.position() - readPosition
        if (consumed > 0) {
            if (!c.tryReadExact(consumed)) throw IllegalStateException("Consumed more bytes than availalbe")

            readPosition = buffer.carryIndex(buffer.position())

            buffer.prepareBuffer(readByteOrder, readPosition, c.remaining)

            c.completeRead(consumed)
            resumeWriteOp()
        }

        return consumed
    }

    private suspend fun readUTF8LineToAscii(out: Appendable, limit: Int): Boolean {
        if (state === ReadWriteBufferState.Terminated) return false

        var cr = false
        var consumed = 0
        var unicodeStarted = false

        val found = lookAheadFast(false) { buffer, last ->
            while (buffer.hasRemaining()) {
                val v = buffer.get().toInt() and 0xff
                when {
                    v == 0x0d -> {
                        cr = true
                    }
                    v == 0x0a -> {
                        return@lookAheadFast false
                    }
                    cr -> {
                        cr = false
                        buffer.position(buffer.position() - 1)
                        return@lookAheadFast false
                    }
                    v and 0x80 == 0 -> {
                        if (consumed == limit) throw BufferOverflowException()
                        consumed++
                        out.append(v.toChar())
                    }
                    else -> { // unicode character
                        buffer.position(buffer.position() - 1)
                        unicodeStarted = true
                        return@lookAheadFast false
                    }
                }
            }

            !last
        }

        if (found && !unicodeStarted) return true
        return readUTF8LineToUtf8(out, limit - consumed, cr, consumed)
    }

    private suspend fun readUTF8LineToUtf8(out: Appendable, limit: Int, cr0: Boolean, consumed0: Int): Boolean {
        var cr1 = cr0
        var consumed1 = 0
        var value = 0
        var byteCount = 0

        val found = lookAheadFast(false) { buffer, last ->
            while (buffer.hasRemaining()) {
                val v = buffer.get().toInt() and 0xff
                when {
                    v == 0x0d -> {
                        cr1 = true
                    }
                    v == 0x0a -> {
                        return@lookAheadFast false
                    }
                    cr1 -> {
                        cr1 = false
                        buffer.position(buffer.position() - 1)
                        return@lookAheadFast false
                    }
                    v and 0x80 == 0 -> {
                        if (byteCount != 0) throw MalformedInputException(0)
                        if (consumed1 == limit) throw BufferOverflowException()
                        consumed1++
                        out.append(v.toChar())
                    }
                    byteCount == 0 -> {
                        // first unicode byte

                        if (consumed1 == limit) {
                            throw BufferOverflowException()
                        }

                        var mask = 0x80
                        value = v

                        for (i in 1..6) { // TODO do we support 6 bytes unicode?
                            if (value and mask != 0) {
                                value = value and mask.inv()
                                mask = mask shr 1
                                byteCount++
                            } else {
                                break
                            }
                        }

                        byteCount--
                    }
                    else -> {
                        // trailing unicode byte
                        value = (value shl 6) or (v and 0x7f)
                        byteCount--

                        if (byteCount == 0) {
                            if (java.lang.Character.isBmpCodePoint(value)) {
                                if (consumed1 == limit) throw BufferOverflowException()

                                out.append(value.toChar())
                                consumed1++
                            } else if (!java.lang.Character.isValidCodePoint(value)) {
                                throw IllegalArgumentException("Malformed code-point ${Integer.toHexString(value)} found")
                            } else {
                                if (consumed1 + 1 >= limit) throw BufferOverflowException()

                                val low = java.lang.Character.lowSurrogate(value)
                                val high = java.lang.Character.highSurrogate(value)

                                out.append(high)
                                out.append(low)

                                consumed1 += 2
                            }

                            value = 0
                        }
                    }
                }
            }

            !last
        }

        if (found) return true

        return readUTF8LineToUtf8Suspend(out, limit, cr1, consumed1 + consumed0)
    }

    private suspend fun readUTF8LineToUtf8Suspend(out: Appendable, limit: Int, cr0: Boolean, consumed0: Int): Boolean {
        var cr1 = cr0
        var consumed1 = 0
        var value = 0
        var byteCount = 0
        var last1 = false

        lookAheadSuspend { buffer, last ->
            last1 = last

            while (buffer.hasRemaining()) {
                val v = buffer.get().toInt() and 0xff
                when {
                    v == 0x0d -> {
                        cr1 = true
                    }
                    v == 0x0a -> {
                        return@lookAheadSuspend false
                    }
                    cr1 -> {
                        cr1 = false
                        buffer.position(buffer.position() - 1)
                        return@lookAheadSuspend false
                    }
                    v and 0x80 == 0 -> {
                        if (byteCount != 0) throw MalformedInputException(0)
                        if (consumed1 == limit) throw BufferOverflowException()
                        consumed1++
                        out.append(v.toChar())
                    }
                    byteCount == 0 -> {
                        // first unicode byte

                        if (consumed1 == limit) {
                            throw BufferOverflowException()
                        }

                        var mask = 0x80
                        value = v

                        for (i in 1..6) { // TODO do we support 6 bytes unicode?
                            if (value and mask != 0) {
                                value = value and mask.inv()
                                mask = mask shr 1
                                byteCount++
                            } else {
                                break
                            }
                        }

                        byteCount--
                    }
                    else -> {
                        // trailing unicode byte
                        value = (value shl 6) or (v and 0x7f)
                        byteCount--

                        if (byteCount == 0) {
                            if (java.lang.Character.isBmpCodePoint(value)) {
                                if (consumed1 == limit) throw BufferOverflowException()

                                out.append(value.toChar())
                                consumed1++
                            } else if (!java.lang.Character.isValidCodePoint(value)) {
                                throw IllegalArgumentException("Malformed code-point ${Integer.toHexString(value)} found")
                            } else {
                                if (consumed1 + 1 >= limit) throw BufferOverflowException()

                                val low = java.lang.Character.lowSurrogate(value)
                                val high = java.lang.Character.highSurrogate(value)

                                out.append(high)
                                out.append(low)

                                consumed1 += 2
                            }

                            value = 0
                        }
                    }
                }
            }

            !last
        }

        return (consumed1 > 0 || consumed0 > 0 || !last1)
    }

    suspend override fun <A : Appendable> readUTF8LineTo(out: A, limit: Int): Boolean {
        return readUTF8LineToAscii(out, limit)
    }

    private fun resumeWriteOp() {
        WriteOp.getAndSet(this, null)?.apply { if (closed == null) resume(Unit) else resumeWithException(closed!!.sendException) }
    }

    protected fun resumeClosed(cause: Throwable?) {
        ReadOp.getAndSet(this, null)?.let { c ->
            if (cause != null)
                c.resumeWithException(cause)
            else
                c.resume(state.capacity.remaining > 0)
        }

        WriteOp.getAndSet(this, null)?.tryResumeWithException(cause ?: ClosedSendChannelException(null))
    }

    protected tailrec suspend fun readSuspend(size: Int): Boolean {
        if (state.capacity.remaining >= size) return true

        closed?.let { c ->
            if (c.cause == null) return false
            throw c.cause
        }

        if (!readSuspendImpl(size)) return false

        return readSuspend(size)
    }

    private suspend fun readSuspendImpl(size: Int): Boolean {
        if (state.capacity.remaining >= size) return true

        return suspendCancellableCoroutine(holdCancellability = true) { c ->
            do {
                if (state.capacity.remaining >= size) {
                    c.resume(true)
                    break
                }

                closed?.let {
                    if (it.cause == null && state.capacity.remaining == 0) {
                        c.resume(false)
                        return@suspendCancellableCoroutine
                    } else if (it.cause != null) {
                        c.resumeWithException(it.cause)
                        return@suspendCancellableCoroutine
                    }
                }
            } while (!setContinuation({ readOp }, ReadOp, c, { closed == null && state.capacity.remaining < size }))
        }
    }

    protected suspend fun writeSuspend(size: Int) {
        closed?.sendException?.let { throw it }

        while (state.capacity.capacity < size && state !== ReadWriteBufferState.IdleEmpty && closed == null) {
            suspendCancellableCoroutine<Unit>(holdCancellability = true) { c ->
                do {
                    closed?.sendException?.let { throw it }
                    if (state.capacity.capacity >= size || state === ReadWriteBufferState.IdleEmpty) {
                        c.resume(Unit)
                        break
                    }
                } while (!setContinuation({ writeOp }, WriteOp, c, { closed == null && state.capacity.capacity < size && state !== ReadWriteBufferState.IdleEmpty }))

                flush()
            }
        }

        closed?.sendException?.let { throw it }
    }

    private inline fun <T, C : CancellableContinuation<T>> setContinuation(getter: () -> C?, updater: AtomicReferenceFieldUpdater<ByteBufferChannel, C?>, continuation: C, predicate: () -> Boolean): Boolean {
        while (true) {
            val current = getter()
            if (current != null) throw IllegalStateException("Operation is already in progress")

            if (!predicate()) {
                return false
            }

            if (updater.compareAndSet(this, null, continuation)) {
                if (predicate() || !updater.compareAndSet(this, continuation, null)) {
                    continuation.initCancellability()
                    return true
                }

                return false
            }
        }
    }

    private fun newBuffer(): ReadWriteBufferState.Initial {
        val result = pool.borrow()

        result.readBuffer.order(readByteOrder.forNio)
        result.writeBuffer.order(writeByteOrder.forNio)
        result.capacity.reset()

        return result
    }

    private fun releaseBuffer(buffer: ReadWriteBufferState.Initial) {
        pool.recycle(buffer)
    }

    private inline fun updateState(block: (ReadWriteBufferState) -> ReadWriteBufferState?): Pair<ReadWriteBufferState, ReadWriteBufferState> {
        val p = update({ state }, State, block)
        return p
    }

    private inline fun <T : Any> update(getter: () -> T, updater: AtomicReferenceFieldUpdater<ByteBufferChannel, T>, block: (old: T) -> T?): Pair<T, T> {
        while (true) {
            val old = getter()
            val newValue = block(old) ?: continue
            if (old === newValue || updater.compareAndSet(this, old, newValue)) return Pair(old, newValue)
        }
    }

    companion object {
        internal const val ReservedSize = 8
        private const val ReservedLongIndex = -8

        private val State = updater(ByteBufferChannel::state)

        private val WriteOp = updater(ByteBufferChannel::writeOp)
        private val ReadOp = updater(ByteBufferChannel::readOp)
        private val ClosedOp = updater(ByteBufferChannel::closed)
    }

    protected class ClosedElement(val cause: Throwable?) {
        val sendException: Throwable
            get() = cause ?: ClosedSendChannelException("The channel was closed")

        companion object {
            val EmptyCause = ClosedElement(null)
        }
    }

}

internal typealias ReadElement = CancellableContinuation<Boolean>
internal typealias WriteElement = CancellableContinuation<Unit>
