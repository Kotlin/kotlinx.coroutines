@file:Suppress("UsePropertyAccessSyntax") // for ByteBuffer.getShort/getInt/etc

package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.io.internal.*
import kotlinx.coroutines.experimental.io.packet.*
import kotlinx.io.core.*
import kotlinx.io.core.ByteReadPacket
import kotlinx.io.pool.*
import java.io.EOFException
import java.nio.*
import java.util.concurrent.atomic.*

internal const val DEFAULT_CLOSE_MESSAGE = "Byte channel was closed"

// implementation for ByteChannel
internal class ByteBufferChannel(
        override val autoFlush: Boolean,
        private val pool: ObjectPool<ReadWriteBufferState.Initial> = BufferObjectPool,
        private val reservedSize: Int = RESERVED_SIZE
) : ByteChannel, LookAheadSuspendSession {
    // internal constructor for reading of byte buffers
    constructor(content: ByteBuffer) : this(false, BufferObjectNoPool, 0) {
        state = ReadWriteBufferState.Initial(content.slice(), 0).apply {
            capacity.resetForRead()
        }.startWriting()
        restoreStateAfterWrite()
        close()
        tryTerminate()
    }

    @Volatile
    private var state: ReadWriteBufferState = ReadWriteBufferState.IdleEmpty

    @Volatile
    private var closed: ClosedElement? = null

    @Volatile
    private var delegatedTo: ByteBufferChannel? = null
    private var delegateClose: Boolean = false

    @Volatile
    private var readOp: CancellableContinuation<Boolean>? = null

    @Volatile
    private var writeOp: CancellableContinuation<Unit>? = null

    private var readPosition = 0
    private var writePosition = 0

    override var readByteOrder: ByteOrder = ByteOrder.BIG_ENDIAN
    override var writeByteOrder: ByteOrder = ByteOrder.BIG_ENDIAN

    override val availableForRead: Int
        get() = state.capacity.availableForRead

    override val availableForWrite: Int
        get() = state.capacity.availableForWrite

    override val isClosedForRead: Boolean
        get() = state === ReadWriteBufferState.Terminated

    override val isClosedForWrite: Boolean
        get() = closed != null

    @Volatile
    override var totalBytesRead: Long = 0L
        private set

    @Volatile
    override var totalBytesWritten: Long = 0L
        private set

    override fun close(cause: Throwable?): Boolean {
        if (closed != null) return false
        val newClosed = if (cause == null) ClosedElement.EmptyCause else ClosedElement(cause)
        state.capacity.flush()
        if (!Closed.compareAndSet(this, null, newClosed)) return false
        state.capacity.flush()
        if (state.capacity.isEmpty() || cause != null) tryTerminate()
        resumeClosed(cause)

        if (state === ReadWriteBufferState.Terminated) {
            delegatedTo?.close(cause)
        }

        return true
    }

    override fun flush() {
        delegatedTo?.let { delegated -> delegated.flush(); return }

        if (!state.capacity.flush()) return
        resumeReadOp()
        if (availableForWrite > 0) resumeWriteOp()
    }

    private fun ByteBuffer.prepareBuffer(order: ByteOrder, position: Int, available: Int) {
        require(position >= 0)
        require(available >= 0)

        val bufferLimit = capacity() - reservedSize
        val virtualLimit = position + available

        order(order.nioOrder)
        limit(virtualLimit.coerceAtMost(bufferLimit))
        position(position)
    }

    private fun setupStateForWrite(): ByteBuffer? {
        var _allocated: ReadWriteBufferState.Initial? = null
        val (old, newState) = updateState { state ->
            when (state) {
                ReadWriteBufferState.IdleEmpty -> {
                    if (delegatedTo != null) {
                        ReadWriteBufferState.Terminated
                    } else {
                        val allocated = _allocated ?: newBuffer().also { _allocated = it }
                        allocated.startWriting()
                    }
                }
                ReadWriteBufferState.Terminated -> {
                    if (delegatedTo != null) {
                        return null
                    }

                    throw closed!!.sendException
                }
                else -> {
                    state.startWriting()
                }
            }
        }

        if (delegatedTo != null && state === ReadWriteBufferState.Terminated) {
            ReadOp.getAndSet(this, null)?.resume(false)
            return null
        }

        val buffer = newState.writeBuffer

        _allocated?.let { allocated ->
            if (old !== ReadWriteBufferState.IdleEmpty) {
                releaseBuffer(allocated)
            }
        }
        return buffer.apply {
            prepareBuffer(writeByteOrder, writePosition, newState.capacity.availableForWrite)
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
                ReadWriteBufferState.Terminated -> closed?.cause?.let { throw it } ?: return null
                ReadWriteBufferState.IdleEmpty -> closed?.cause?.let { throw it } ?: return null
                else -> {
                    if (state.capacity.availableForRead == 0) return null
                    state.startReading()
                }
            }
        }

        return newState.readBuffer.apply {
            prepareBuffer(readByteOrder, readPosition, newState.capacity.availableForRead)
        }
    }

    private fun restoreStateAfterRead() {
        var toRelease: ReadWriteBufferState.IdleNonEmpty? = null

        val (_, newState) = updateState { state ->
            toRelease?.let {
                it.capacity.resetForWrite()
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

    private fun setupDelegateTo(delegate: ByteBufferChannel, delegateClose: Boolean) {
        require(this !== delegate)

        this.delegateClose = delegateClose
        this.delegatedTo = delegate
        resumeWriteOp()

        val alreadyClosed = closed
        if (alreadyClosed != null) {
            if (alreadyClosed.cause != null) delegate.close(alreadyClosed.cause)
            else if (delegateClose) delegate.close()
            else delegate.flush()
        } else {
            flush()
        }
    }

    private fun tryTerminate(): Boolean {
        val closed = closed
        val delegate = delegatedTo

        if (closed == null && delegate == null) return false

        var toRelease: ReadWriteBufferState.Initial? = null

        updateState { state ->
            when {
                state === ReadWriteBufferState.Terminated -> return true
                state === ReadWriteBufferState.IdleEmpty -> ReadWriteBufferState.Terminated
                closed?.cause != null && state is ReadWriteBufferState.IdleNonEmpty -> {
                    toRelease = state.initial
                    ReadWriteBufferState.Terminated
                }
                else -> return false
            }
        }

        toRelease?.let { buffer ->
            if (state === ReadWriteBufferState.Terminated) {
                releaseBuffer(buffer)
            }
        }

        if (closed != null) {
            WriteOp.getAndSet(this, null)?.resumeWithException(closed.sendException)
            ReadOp.getAndSet(this, null)?.apply {
                if (closed.cause != null) resumeWithException(closed.cause) else resume(false)
            }
        } else if (delegate != null) {
            WriteOp.getAndSet(this, null)?.resumeWithException(IllegalStateException("Delegation preparation is in progress"))
            ReadOp.getAndSet(this, null)?.resume(false) // send EOF to delegator copy loop
        }

        return true
    }

    private fun ByteBuffer.carryIndex(idx: Int) = if (idx >= capacity() - reservedSize) idx - (capacity() - reservedSize) else idx

    private inline fun writing(block: ByteBufferChannel.(ByteBuffer, RingBufferCapacity) -> Unit) {
        val buffer: ByteBuffer
        val capacity: RingBufferCapacity

        var current = this
        while (true) {
            val bb = current.setupStateForWrite()
            if (bb == null && current.state === ReadWriteBufferState.Terminated) {
                current = current.delegatedTo!!
            } else if (bb == null) {
                return
            } else {
                buffer = bb
                capacity = current.state.capacity
                break
            }
        }

        try {
            current.closed?.let { throw it.sendException }
            block(current, buffer, capacity)
        } finally {
            if (capacity.isFull() || current.autoFlush) current.flush()
            current.restoreStateAfterWrite()
            current.tryTerminate()
        }
    }

    private inline fun reading(block: ByteBuffer.(RingBufferCapacity) -> Boolean): Boolean {
        val buffer = setupStateForRead() ?: return false
        val capacity = state.capacity
        try {
            if (capacity.availableForRead == 0) return false

            return block(buffer, capacity)
        } finally {
            restoreStateAfterRead()
            tryTerminate()
        }
    }

    private tailrec fun readAsMuchAsPossible(dst: ByteBuffer, consumed0: Int = 0): Int {
        var consumed = 0

        val rc = reading {
            val position = position()
            val remaining = limit() - position

            val part = it.tryReadAtMost(minOf(remaining, dst.remaining()))
            if (part > 0) {
                consumed += part

                limit(position + part)
                dst.put(this)

                bytesRead(it, part)
                true
            } else {
                false
            }
        }

        return if (rc && dst.hasRemaining() && state.capacity.availableForRead > 0)
            readAsMuchAsPossible(dst, consumed0 + consumed)
        else consumed + consumed0
    }

    private tailrec fun readAsMuchAsPossible(dst: BufferView, consumed0: Int = 0): Int {
        var consumed = 0

        val rc = reading {
            val dstSize = dst.writeRemaining
            val part = it.tryReadAtMost(minOf(remaining(), dstSize))
            if (part > 0) {
                consumed += part

                if (dstSize < remaining()) {
                    limit(position() + dstSize)
                }
                dst.write(this)

                bytesRead(it, part)
                true
            } else {
                false
            }
        }

        return if (rc && dst.canWrite() && state.capacity.availableForRead > 0)
            readAsMuchAsPossible(dst, consumed0 + consumed)
        else consumed + consumed0
    }


    private tailrec fun readAsMuchAsPossible(dst: ByteArray, offset: Int, length: Int, consumed0: Int = 0): Int {
        var consumed = 0

        val rc = reading {
            val part = it.tryReadAtMost(minOf(remaining(), length))
            if (part > 0) {
                consumed += part
                get(dst, offset, part)

                bytesRead(it, part)
                true
            } else {
                false
            }
        }

        return if (rc && consumed < length && state.capacity.availableForRead > 0)
            readAsMuchAsPossible(dst, offset + consumed, length - consumed, consumed0 + consumed)
        else consumed + consumed0
    }

    suspend override fun readFully(dst: ByteArray, offset: Int, length: Int) {
        val consumed = readAsMuchAsPossible(dst, offset, length)

        if (consumed < length) {
            readFullySuspend(dst, offset + consumed, length - consumed)
        }
    }

    suspend override fun readFully(dst: ByteBuffer): Int {
        val rc = readAsMuchAsPossible(dst)
        if (!dst.hasRemaining()) return rc

        return readFullySuspend(dst, rc)
    }

    private suspend fun readFullySuspend(dst: ByteBuffer, rc0: Int): Int {
        var copied = rc0

        while (dst.hasRemaining()) {
            if (!readSuspend(1)) throw ClosedReceiveChannelException("Unexpected EOF: expected ${dst.remaining()} more bytes")
            copied += readAsMuchAsPossible(dst)
        }

        return copied
    }

    private suspend tailrec fun readFullySuspend(dst: ByteArray, offset: Int, length: Int) {
        if (!readSuspend(1)) throw ClosedReceiveChannelException("Unexpected EOF: expected $length more bytes")

        val consumed = readAsMuchAsPossible(dst, offset, length)

        if (consumed < length) {
            readFullySuspend(dst, offset + consumed, length - consumed)
        }
    }

    suspend override fun readAvailable(dst: ByteArray, offset: Int, length: Int): Int {
        val consumed = readAsMuchAsPossible(dst, offset, length)

        if (consumed == 0 && closed != null) {
            if (state.capacity.flush()) {
                return readAsMuchAsPossible(dst, offset, length)
            } else {
                return -1
            }
        }
        else if (consumed > 0 || length == 0) return consumed

        return readAvailableSuspend(dst, offset, length)
    }

    suspend override fun readAvailable(dst: ByteBuffer): Int {
        val consumed = readAsMuchAsPossible(dst)

        if (consumed == 0 && closed != null) {
            if (state.capacity.flush()) {
                return readAsMuchAsPossible(dst)
            } else {
                return -1
            }
        }
        else if (consumed > 0 || !dst.hasRemaining()) return consumed

        return readAvailableSuspend(dst)
    }

    suspend override fun readAvailable(dst: BufferView): Int {
        val consumed = readAsMuchAsPossible(dst)

        if (consumed == 0 && closed != null) {
            if (state.capacity.flush()) {
                return readAsMuchAsPossible(dst)
            } else {
                return -1
            }
        }
        else if (consumed > 0 || !dst.canWrite()) return consumed

        return readAvailableSuspend(dst)
    }

    private suspend fun readAvailableSuspend(dst: ByteArray, offset: Int, length: Int): Int {
        if (!readSuspend(1)) return -1
        return readAvailable(dst, offset, length)
    }

    private suspend fun readAvailableSuspend(dst: ByteBuffer): Int {
        if (!readSuspend(1)) return -1
        return readAvailable(dst)
    }

    private suspend fun readAvailableSuspend(dst: BufferView): Int {
        if (!readSuspend(1)) return -1
        return readAvailable(dst)
    }

    suspend override fun readPacket(size: Int, headerSizeHint: Int): ByteReadPacket {
        closed?.cause?.let { throw it }

        if (size == 0) return ByteReadPacket.Empty

        val builder = BytePacketBuilder(headerSizeHint)
        val buffer = BufferPool.borrow()
        var remaining = size

        try {
            while (remaining > 0) {
                buffer.clear()
                if (buffer.remaining() > remaining) {
                    buffer.limit(remaining)
                }

                val rc = readAsMuchAsPossible(buffer)
                if (rc == 0) break

                buffer.flip()
                builder.writeFully(buffer)

                remaining -= rc
            }
        } catch (t: Throwable) {
            BufferPool.recycle(buffer)
            builder.release()
            throw t
        }

        return if (remaining == 0) {
            BufferPool.recycle(buffer)
            builder.build()
        } else {
            readPacketSuspend(remaining, builder, buffer)
        }
    }

    private suspend fun readPacketSuspend(size: Int, builder: ByteWritePacketImpl, buffer: ByteBuffer): ByteReadPacket {
        var remaining = size

        try {
            while (remaining > 0) {
                buffer.clear()
                if (buffer.remaining() > remaining) {
                    buffer.limit(remaining)
                }

                val rc = readFully(buffer)

                buffer.flip()
                builder.writeFully(buffer)

                remaining -= rc
            }


            return builder.build()
        } catch (t: Throwable) {
            builder.release()
            throw t
        } finally {
            BufferPool.recycle(buffer)
        }
    }

    suspend override fun readByte(): Byte {
        var b: Byte = 0

        val rc = reading {
            if (it.tryReadExact(1)) {
                b = get()
                bytesRead(it, 1)
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
                bytesRead(it, 1)
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

    suspend override fun readShort(): Short {
        var sh: Short = 0

        val rc = reading {
            if (it.tryReadExact(2)) {
                if (remaining() < 2) rollBytes(2)
                sh = getShort()
                bytesRead(it, 2)
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

    suspend override fun readInt(): Int {
        var i = 0

        val rc = reading {
            if (it.tryReadExact(4)) {
                if (remaining() < 4) rollBytes(4)
                i = getInt()
                bytesRead(it, 4)
                true
            } else false
        }

        return if (rc) {
            i
        } else {
            readIntSuspend()
        }
    }

    private suspend fun readIntSuspend(): Int {
        if (!readSuspend(4)) throw ClosedReceiveChannelException("EOF while an int expected")
        return readInt()
    }

    suspend override fun readLong(): Long {
        var i = 0L

        val rc = reading {
            if (it.tryReadExact(8)) {
                if (remaining() < 8) rollBytes(8)
                i = getLong()
                bytesRead(it, 8)
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
                bytesRead(it, 8)
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
                bytesRead(it, 4)
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

    private fun ByteBuffer.rollBytes(n: Int) {
        limit(position() + n)
        for (i in 1..n - remaining()) {
            put(capacity() + ReservedLongIndex + i, get(i))
        }
    }

    private fun ByteBuffer.carry() {
        val base = capacity() - reservedSize
        for (i in base until position()) {
            put(i - base, get(i))
        }
    }

    private fun ByteBuffer.bytesWritten(c: RingBufferCapacity, n: Int) {
        require(n >= 0)

        writePosition = carryIndex(writePosition + n)
        c.completeWrite(n)
        totalBytesWritten += n
    }

    private fun ByteBuffer.bytesRead(c: RingBufferCapacity, n: Int) {
        require(n >= 0)

        readPosition = carryIndex(readPosition + n)
        c.completeRead(n)
        totalBytesRead += n
        resumeWriteOp()
    }

    private suspend fun <R> delegation(delegate: ByteBufferChannel, block: suspend (ByteBufferChannel) -> R): R {
        restoreStateAfterWrite()

        while (true) {
            if (tryTerminate()) {
                return block(delegate)
            } else {
                writeSuspend(Int.MAX_VALUE) // wait for delegator loop complete
            }
        }
    }

    suspend override fun writeByte(b: Byte) {
        val buffer = setupStateForWrite() ?: return delegatedTo!!.writeByte(b)
        val c = state.capacity

        return tryWriteByte(buffer, b, c)
    }

    private suspend fun tryWriteByte(buffer: ByteBuffer, b: Byte, c: RingBufferCapacity) {
        if (!c.tryWriteExact(1)) {
            return writeByteSuspend(buffer, b, c)
        }

        doWrite(buffer, b, c)
    }

    private fun doWrite(buffer: ByteBuffer, b: Byte, c: RingBufferCapacity) {
        buffer.put(b)
        buffer.bytesWritten(c, 1)
        if (c.isFull() || autoFlush) flush()
        restoreStateAfterWrite()
    }

    private suspend fun writeByteSuspend(buffer: ByteBuffer, b: Byte, c: RingBufferCapacity) {
        try {
            writeSuspend(1)
        } catch (t: Throwable) {
            restoreStateAfterWrite()
            tryTerminate()
            throw t
        }

        delegatedTo?.let { delegate ->
            return delegation(delegate) { it.writeByte(b) }
        }

        buffer.prepareBuffer(writeByteOrder, writePosition, c.availableForWrite)
        return tryWriteByte(buffer, b, c)
    }

    suspend override fun writeShort(s: Short) {
        val buffer = setupStateForWrite() ?: return delegatedTo!!.writeShort(s)
        val c = state.capacity

        return tryWriteShort(buffer, s, c)
    }

    private fun doWrite(buffer: ByteBuffer, s: Short, c: RingBufferCapacity) {
        buffer.apply {
            if (remaining() < 2) {
                limit(capacity())
                putShort(s)
                carry()
            } else {
                putShort(s)
            }

            bytesWritten(c, 2)
        }

        if (c.isFull() || autoFlush) flush()
        restoreStateAfterWrite()
    }

    private suspend fun tryWriteShort(buffer: ByteBuffer, s: Short, c: RingBufferCapacity) {
        if (!c.tryWriteExact(2)) {
            return writeShortSuspend(buffer, s, c)
        }

        return doWrite(buffer, s, c)
    }

    private suspend fun writeShortSuspend(buffer: ByteBuffer, s: Short, c: RingBufferCapacity) {
        try {
            writeSuspend(2)
        } catch (t: Throwable) {
            restoreStateAfterWrite()
            tryTerminate()
            throw t
        }

        delegatedTo?.let { delegate ->
            return delegation(delegate) { it.writeShort(s) }
        }

        buffer.prepareBuffer(writeByteOrder, writePosition, c.availableForWrite)
        return tryWriteShort(buffer, s, c)
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
            if (c.isFull() || autoFlush) flush()
            restoreStateAfterWrite()
            tryTerminate()
            return true
        }

        return false
    }

    suspend override fun writeInt(i: Int) {
        val buffer = setupStateForWrite() ?: return delegatedTo!!.writeInt(i)
        val c = state.capacity

        if (!buffer.tryWriteInt(i, c)) {
            return buffer.writeIntSuspend(i, c)
        }
    }

    private tailrec suspend fun ByteBuffer.writeIntSuspend(i: Int, c: RingBufferCapacity) {
        try {
            writeSuspend(4)
        } catch (t: Throwable) {
            restoreStateAfterWrite()
            tryTerminate()
            throw t
        }

        delegatedTo?.let { delegate ->
            return delegation(delegate) { it.writeInt(i) }
        }

        prepareBuffer(writeByteOrder, writePosition, c.availableForWrite)
        if (!tryWriteInt(i, c)) {
            return writeIntSuspend(i, c)
        }
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
            if (c.isFull() || autoFlush) flush()
            restoreStateAfterWrite()
            tryTerminate()
            return true
        }

        return false
    }

    suspend override fun writeLong(l: Long) {
        val buffer = setupStateForWrite() ?: return delegatedTo!!.writeLong(l)
        val c = state.capacity

        if (!buffer.tryWriteLong(l, c)) {
            return buffer.writeLongSuspend(l, c)
        }
    }

    private tailrec suspend fun ByteBuffer.writeLongSuspend(l: Long, c: RingBufferCapacity) {
        try {
            writeSuspend(8)
        } catch (t: Throwable) {
            restoreStateAfterWrite()
            tryTerminate()
            throw t
        }

        delegatedTo?.let { delegate ->
            return delegation(delegate) { it.writeLong(l) }
        }

        prepareBuffer(writeByteOrder, writePosition, c.availableForWrite)
        if (!tryWriteLong(l, c)) {
            return writeLongSuspend(l, c)
        }
    }

    suspend override fun writeDouble(d: Double) {
        writeLong(java.lang.Double.doubleToRawLongBits(d))
    }

    suspend override fun writeFloat(f: Float) {
        writeInt(java.lang.Float.floatToRawIntBits(f))
    }

    suspend override fun writeAvailable(src: ByteBuffer): Int {
        val copied = writeAsMuchAsPossible(src)
        if (copied > 0) return copied

        return writeAvailableSuspend(src)
    }

    suspend override fun writeAvailable(src: BufferView): Int {
        val copied = writeAsMuchAsPossible(src)
        if (copied > 0) return copied

        return writeAvailableSuspend(src)
    }

    private suspend fun writeAvailableSuspend(src: ByteBuffer): Int {
        while (true) {
            writeSuspend(1) // here we don't need to restoreStateAfterWrite as write copy loop doesn't hold state

            delegatedTo?.let { delegate ->
                return delegation(delegate) { it.writeAvailable(src) }
            }

            val copied = writeAvailable(src)
            if (copied > 0) return copied
        }
    }

    private suspend fun writeAvailableSuspend(src: BufferView): Int {
        while (true) {
            writeSuspend(1)

            delegatedTo?.let { delegate ->
                return delegation(delegate) { it.writeAvailable(src) }
            }

            val copied = writeAvailable(src)
            if (copied > 0) return copied
        }
    }

    suspend override fun writeFully(src: ByteBuffer) {
        writeAsMuchAsPossible(src)
        if (!src.hasRemaining()) return

        return writeFullySuspend(src)
    }

    suspend override fun writeFully(src: BufferView) {
        writeAsMuchAsPossible(src)
        if (!src.canRead()) return

        return writeFullySuspend(src)
    }

    private suspend fun writeFullySuspend(src: ByteBuffer) {
        while (src.hasRemaining()) {
            writeSuspend(1)

            delegatedTo?.let { delegate ->
                return delegation(delegate) { it.writeFully(src) }
            }

            writeAsMuchAsPossible(src)
        }
    }

    private suspend fun writeFullySuspend(src: BufferView) {
        while (src.canRead()) {
            writeSuspend(1)

            delegatedTo?.let { delegate ->
                return delegation(delegate) { it.writeFully(src) }
            }

            writeAsMuchAsPossible(src)
        }
    }

    internal suspend fun joinFrom(src: ByteBufferChannel, delegateClose: Boolean) {
        src.setupDelegateTo(this, delegateClose)
        copyDirect(src, Long.MAX_VALUE, leaveOnDelegation = true)

        if (delegateClose && src.isClosedForRead) {
            close()
        } else {
            flush()
        }
    }

    internal suspend fun copyDirect(src: ByteBufferChannel, limit: Long, leaveOnDelegation: Boolean): Long {
        if (limit == 0L || src.isClosedForRead) return 0L
        val autoFlush = autoFlush
        val byteOrder = writeByteOrder

        try {
            var copied = 0L
            writing { dstBuffer, state ->
                while (copied < limit) {
                    var avWBefore = state.availableForWrite
                    if (avWBefore == 0) {
                        writeSuspend(1)
                        if (delegatedTo != null) break
                        avWBefore = state.availableForWrite
                    }

                    dstBuffer.prepareBuffer(byteOrder, writePosition, avWBefore)

                    var partSize = 0

                    val rc = src.reading { srcState ->
                        val srcBuffer = this

                        val rem = minOf(srcBuffer.remaining().toLong(), dstBuffer.remaining().toLong(), limit - copied).toInt()
                        val n = state.tryWriteAtMost(rem)
                        if (n > 0) {
                            if (!srcState.tryReadExact(n)) throw AssertionError()

                            srcBuffer.limit(srcBuffer.position() + n)

                            dstBuffer.put(srcBuffer)
                            partSize = n

                            with(src) {
                                srcBuffer.bytesRead(srcState, n)
                            }
                        }

                        true
                    }

                    if (rc) {
                        dstBuffer.bytesWritten(state, partSize)
                        copied += partSize

                        if (avWBefore - partSize == 0 || autoFlush) {
                            flush()
                        }
                    } else {
                        if (src.isClosedForRead) break

                        flush()

                        if (leaveOnDelegation) {
                            if (src.tryShutdownForDelegation()) break
                            else if (src.state.capacity.flush()) {
                                src.resumeWriteOp()
                                continue
                            }
                        }

                        if (!src.readSuspend(1)) break
                    }
                }
            }

            if (autoFlush) {
                flush()
            }

            delegatedTo?.let { delegate ->
                return copied + delegate.copyDirect(src, limit - copied, leaveOnDelegation)
            }

            return copied
        } catch (t: Throwable) {
            close(t)
            throw t
        }
    }

    private fun tryShutdownForDelegation(): Boolean {
        if (delegatedTo == null) return false

        updateState { before ->
            if (before === ReadWriteBufferState.Terminated) return true
            if (before === ReadWriteBufferState.IdleEmpty) ReadWriteBufferState.Terminated
            else return false
        }

        return true
    }

    private fun writeAsMuchAsPossible(src: ByteBuffer): Int {
        writing { dst, state ->
            var written = 0
            val srcLimit = src.limit()

            do {
                val srcRemaining = srcLimit - src.position()
                if (srcRemaining == 0) break
                val possibleSize = state.tryWriteAtMost(minOf(srcRemaining, dst.remaining()))
                if (possibleSize == 0) break
                require(possibleSize > 0)

                src.limit(src.position() + possibleSize)
                dst.put(src)

                written += possibleSize

                dst.prepareBuffer(writeByteOrder, dst.carryIndex(writePosition + written), state.availableForWrite)
            } while (true)

            src.limit(srcLimit)

            dst.bytesWritten(state, written)

            return written
        }

        return 0
    }

    private fun writeAsMuchAsPossible(src: BufferView): Int {
        writing { dst, state ->
            var written = 0

            do {
                val srcSize = src.readRemaining
                val possibleSize = state.tryWriteAtMost(minOf(srcSize, dst.remaining()))
                if (possibleSize == 0) break

                src.read(dst, possibleSize)

                written += possibleSize

                dst.prepareBuffer(writeByteOrder, dst.carryIndex(writePosition + written), state.availableForWrite)
            } while (true)

            dst.bytesWritten(state, written)

            return written
        }

        return 0
    }

    private fun writeAsMuchAsPossible(src: ByteArray, offset: Int, length: Int): Int {
        writing { dst, state ->
            var written = 0

            do {
                val possibleSize = state.tryWriteAtMost(minOf(length - written, dst.remaining()))
                if (possibleSize == 0) break
                require(possibleSize > 0)

                dst.put(src, offset + written, possibleSize)
                written += possibleSize

                dst.prepareBuffer(writeByteOrder, dst.carryIndex(writePosition + written), state.availableForWrite)
            } while (true)

            dst.bytesWritten(state, written)

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
        val copied = writeAvailable(src, offset, length)
        return writeFullySuspend(src, offset + copied, length - copied)
    }

    suspend override fun writeAvailable(src: ByteArray, offset: Int, length: Int): Int {
        val size = writeAsMuchAsPossible(src, offset, length)
        if (size > 0) return size
        return writeSuspend(src, offset, length)
    }

    private suspend fun writeSuspend(src: ByteArray, offset: Int, length: Int): Int {
        while (true) {
            writeSuspend(1)

            delegatedTo?.let { delegate ->
                return delegation(delegate) { it.writeAvailable(src, offset, length) }
            }

            val size = writeAsMuchAsPossible(src, offset, length)
            if (size > 0) return size
        }
    }

    override suspend fun write(min: Int, block: (ByteBuffer) -> Unit) {
        require(min > 0) { "min should be positive"}

        var written = false

        writing { dst, state ->
            if (state.availableForWrite >= min) {
                val position = dst.position()
                val l = dst.limit()
                block(dst)
                if (l != dst.limit()) throw IllegalStateException("buffer limit modified")
                val delta = dst.position() - position
                if (delta < 0) throw IllegalStateException("position has been moved backward: pushback is not supported")

                if (!state.tryWriteExact(delta)) throw IllegalStateException()
                dst.bytesWritten(state, delta)
                written = true
            }
        }

        if (!written) {
            return writeBlockSuspend(min, block)
        }
    }

    private suspend fun writeBlockSuspend(min: Int, block: (ByteBuffer) -> Unit) {
        writeSuspend(min)
        delegatedTo?.let { delegate ->
            return delegation(delegate) { it.write(min, block) }
        }
        write(min, block)
    }

    override suspend fun read(min: Int, block: (ByteBuffer) -> Unit) {
        require(min > 0) { "min should be positive" }

        val read = reading {
            if (it.availableForRead >= min) {
                val position = this.position()
                val l = this.limit()
                block(this)
                if (l != this.limit()) throw IllegalStateException("buffer limit modified")
                val delta = position() - position
                if (delta < 0) throw IllegalStateException("position has been moved backward: pushback is not supported")

                if (!it.tryReadExact(delta)) throw IllegalStateException()
                bytesRead(it, delta)
                true
            }
            else false
        }

        if (!read) {
            return readBlockSuspend(min, block)
        }
    }

    private suspend fun readBlockSuspend(min: Int, block: (ByteBuffer) -> Unit) {
        if (!readSuspend(min)) throw EOFException("Got EOF but at least $min bytes were expected")
        read(min, block)
    }

    suspend override fun writePacket(packet: ByteReadPacket) {
        try {
            while (!packet.isEmpty) {
                if (tryWritePacketPart(packet) == 0) break
            }
        } catch (t: Throwable) {
            packet.release()
            throw t
        }

        if (packet.remaining > 0) {
            return writePacketSuspend(packet)
        }
    }

    private suspend fun writePacketSuspend(packet: ByteReadPacket) {
        try {
            while (!packet.isEmpty) {
                writeSuspend(1)
                delegatedTo?.let { delegate ->
                    return delegation(delegate) { it.writePacket(packet) }
                }
                tryWritePacketPart(packet)
            }
        } finally {
            packet.release()
        }
    }

    private fun tryWritePacketPart(packet: ByteReadPacket): Int {
        var copied = 0
        writing { dst, state ->
            val size = state.tryWriteAtMost(minOf(packet.remaining, dst.remaining()))
            if (size > 0) {
                dst.limit(dst.position() + size)
                packet.readFully(dst)
                dst.bytesWritten(state, size)
            }
            copied = size
        }

        return copied
    }

    /**
     * Invokes [visitor] for every available batch until all bytes processed or visitor if visitor returns false.
     * Never invokes [visitor] with empty buffer unless [last] = true. Invokes visitor with last = true at most once
     * even if there are remaining bytes and visitor returned true.
     */
    override suspend fun consumeEachBufferRange(visitor: (buffer: ByteBuffer, last: Boolean) -> Boolean) {
        if (consumeEachBufferRangeFast(false, visitor)) return
        consumeEachBufferRangeSuspend(visitor)
    }

    override fun <R> lookAhead(visitor: LookAheadSession.() -> R): R {
        if (state === ReadWriteBufferState.Terminated) {
            return visitor(TerminatedLookAhead)
        }

        var result: R? = null
        val rc = reading {
            result = visitor(this@ByteBufferChannel)
            true
        }

        if (!rc) {
            return visitor(TerminatedLookAhead)
        }

        return result!!
    }

    suspend override fun <R> lookAheadSuspend(visitor: suspend LookAheadSuspendSession.() -> R): R {
        if (state === ReadWriteBufferState.Terminated) {
            return visitor(TerminatedLookAhead)
        }

        var result: R? = null
        val rc = reading {
            result = visitor(this@ByteBufferChannel)
            true
        }

        if (!rc) {
            if (closed != null || state === ReadWriteBufferState.Terminated) return visitor(TerminatedLookAhead)
            result = visitor(this)
            if (!state.idle && state !== ReadWriteBufferState.Terminated) {
                restoreStateAfterRead()
                tryTerminate()
            }
        }

        return result!!
    }

    override fun consumed(n: Int) {
        require(n >= 0)

        state.let { s ->
            if (!s.capacity.tryReadExact(n)) throw IllegalStateException("Unable to consume $n bytes: not enough available bytes")
            s.readBuffer.bytesRead(s.capacity, n)
        }
    }

    suspend override fun awaitAtLeast(n: Int) {
        if (readSuspend(n) && state.idle) {
            setupStateForRead()
        }
    }

    override fun request(skip: Int, atLeast: Int): ByteBuffer? {
        return state.let { s ->
            val available = s.capacity.availableForRead
            val rp = readPosition

            if (available < atLeast + skip) return null
            if (s.idle || (s !is ReadWriteBufferState.Reading && s !is ReadWriteBufferState.ReadingWriting)) return null

            val buffer = s.readBuffer

            val position = buffer.carryIndex(rp + skip)
            buffer.prepareBuffer(readByteOrder, position, available - skip)

            if (buffer.remaining() >= atLeast) buffer else null
        }
    }

    private inline fun consumeEachBufferRangeFast(last: Boolean, visitor: (buffer: ByteBuffer, last: Boolean) -> Boolean): Boolean {
        if (state === ReadWriteBufferState.Terminated && !last) return false

        val rc = reading {
            do {
                val available = state.capacity.availableForRead

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
            visitor(EmptyByteBuffer, true)
        }

        return rc
    }

    private suspend fun consumeEachBufferRangeSuspend(visitor: (buffer: ByteBuffer, last: Boolean) -> Boolean): Boolean {
        var last = false

        do {
            if (consumeEachBufferRangeFast(last, visitor)) return true
            if (last) return false
            if (!readSuspend(1)) {
                last = true
            }
        } while (true)
    }

    private fun afterBufferVisited(buffer: ByteBuffer, c: RingBufferCapacity): Int {
        val consumed = buffer.position() - readPosition
        if (consumed > 0) {
            if (!c.tryReadExact(consumed)) throw IllegalStateException("Consumed more bytes than available")

            buffer.bytesRead(c, consumed)
            buffer.prepareBuffer(readByteOrder, readPosition, c.availableForRead)
        }

        return consumed
    }

    private suspend fun readUTF8LineToAscii(out: Appendable, limit: Int): Boolean {
        if (state === ReadWriteBufferState.Terminated) return false

        var cr = false
        var consumed = 0
        var unicodeStarted = false
        var eol = false

        consumeEachBufferRangeFast(false) { buffer, last ->
            var forceConsume = false

            val rejected = !buffer.decodeASCII { ch ->
                when {
                    ch == '\r' -> {
                        cr = true
                        true
                    }
                    ch == '\n' -> {
                        eol = true
                        forceConsume = true
                        false
                    }
                    cr -> {
                        cr = false
                        eol = true
                        false
                    }
                    else -> {
                        if (consumed == limit) throw BufferOverflowException()
                        consumed++
                        out.append(ch)
                        true
                    }
                }
            }

            if (cr && last) {
                eol = true
            }

            if (eol && forceConsume) {
                buffer.position(buffer.position() + 1)
            }

            if (rejected && buffer.hasRemaining() && !eol) {
                unicodeStarted = true
                false
            } else
                !eol && !last
        }

        if (eol && !unicodeStarted) return true
        return readUTF8LineToUtf8(out, limit - consumed, cr, consumed)
    }

    private suspend fun readUTF8LineToUtf8(out: Appendable, limit: Int, cr0: Boolean, consumed0: Int): Boolean {
        var cr1 = cr0
        var consumed1 = 0
        var eol = false

        consumeEachBufferRangeFast(false) { buffer, last ->
            var forceConsume = false

            val rc = buffer.decodeUTF8 { ch ->
                when {
                    ch == '\r' -> {
                        cr1 = true
                        true
                    }
                    ch == '\n' -> {
                        eol = true
                        forceConsume = true
                        false
                    }
                    cr1 -> {
                        cr1 = false
                        eol = true
                        false
                    }
                    else -> {
                        if (consumed1 == limit) throw BufferOverflowException()
                        consumed1++
                        out.append(ch)
                        true
                    }
                }
            }

            if (cr1 && last) {
                eol = true
            }

            if (eol && forceConsume) {
                buffer.position(buffer.position() + 1)
            }

            rc != 0 && !eol && !last
        }

        if (eol) return true

        return readUTF8LineToUtf8Suspend(out, limit, cr1, consumed1 + consumed0)
    }

    private suspend fun readUTF8LineToUtf8Suspend(out: Appendable, limit: Int, cr0: Boolean, consumed0: Int): Boolean {
        var cr1 = cr0
        var consumed1 = 0
        var eol = false
        var wrap = 0

        consumeEachBufferRangeSuspend { buffer, last ->
            var forceConsume = false

            val rc = buffer.decodeUTF8 { ch ->
                when {
                    ch == '\r' -> {
                        cr1 = true
                        true
                    }
                    ch == '\n' -> {
                        eol = true
                        forceConsume = true
                        false
                    }
                    cr1 -> {
                        cr1 = false
                        eol = true
                        false
                    }
                    else -> {
                        if (consumed1 == limit) throw BufferOverflowException()
                        consumed1++
                        out.append(ch)
                        true
                    }
                }
            }

            if (cr1 && last) {
                eol = true
            }

            if (eol && forceConsume) {
                buffer.position(buffer.position() + 1)
            }

            wrap = maxOf(0, rc)

            wrap == 0 && !eol && !last
        }

        if (wrap != 0) {
            if (!readSuspend(wrap)) {

            }

            return readUTF8LineToUtf8Suspend(out, limit, cr1, consumed1)
        }

        return (consumed1 > 0 || consumed0 > 0 || eol)
    }

    suspend override fun <A : Appendable> readUTF8LineTo(out: A, limit: Int) = readUTF8LineToAscii(out, limit)

    private fun resumeReadOp() {
        ReadOp.getAndSet(this, null)?.resume(true)
    }

    private fun resumeWriteOp() {
        WriteOp.getAndSet(this, null)?.apply {
            val closed = closed
            if (closed == null) resume(Unit) else resumeWithException(closed.sendException)
        }
    }

    private fun resumeClosed(cause: Throwable?) {
        ReadOp.getAndSet(this, null)?.let { c ->
            if (cause != null)
                c.resumeWithException(cause)
            else
                c.resume(state.capacity.availableForRead > 0)
        }

        WriteOp.getAndSet(this, null)?.tryResumeWithException(cause ?:
            ClosedWriteChannelException(DEFAULT_CLOSE_MESSAGE))
    }

    private tailrec suspend fun readSuspend(size: Int): Boolean {
        val capacity = state.capacity
        if (capacity.availableForRead >= size) return true

        closed?.let { c ->
            if (c.cause != null) throw c.cause
            val afterCapacity = state.capacity
            return afterCapacity.flush() && afterCapacity.availableForRead >= size
        }

        if (!readSuspendImpl(size)) return false

        return readSuspend(size)
    }

    private suspend fun readSuspendImpl(size: Int): Boolean {
        if (state.capacity.availableForRead >= size) return true

        return suspendCancellableCoroutine(holdCancellability = true) { c ->
            do {
                if (state.capacity.availableForRead >= size) {
                    c.resume(true)
                    break
                }

                closed?.let {
                    if (it.cause != null) {
                        c.resumeWithException(it.cause)
                    } else {
                        c.resume(state.capacity.flush() && state.capacity.availableForRead >= size)
                    }
                    return@suspendCancellableCoroutine
                }
            } while (!setContinuation({ readOp }, ReadOp, c, { closed == null && state.capacity.availableForRead < size }))
        }
    }

    private suspend fun writeSuspend(size: Int) {
        while (state.capacity.availableForWrite < size && state !== ReadWriteBufferState.IdleEmpty && delegatedTo == null) {
            suspendCancellableCoroutine<Unit>(holdCancellability = true) { c ->
                do {
                    closed?.sendException?.let { throw it }
                    if (state.capacity.availableForWrite >= size || state === ReadWriteBufferState.IdleEmpty || delegatedTo != null) {
                        c.resume(Unit)
                        break
                    }
                } while (!setContinuation({ writeOp }, WriteOp, c, { closed == null && state.capacity.availableForWrite < size && state !== ReadWriteBufferState.IdleEmpty && delegatedTo == null }))

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

        result.readBuffer.order(readByteOrder.nioOrder)
        result.writeBuffer.order(writeByteOrder.nioOrder)
        result.capacity.resetForWrite()

        return result
    }

    private fun releaseBuffer(buffer: ReadWriteBufferState.Initial) {
        pool.recycle(buffer)
    }

    // todo: replace with atomicfu
    private inline fun updateState(block: (ReadWriteBufferState) -> ReadWriteBufferState?):
        Pair<ReadWriteBufferState, ReadWriteBufferState> = update({ state }, State, block)

    // todo: replace with atomicfu
    private inline fun <T : Any> update(getter: () -> T, updater: AtomicReferenceFieldUpdater<ByteBufferChannel, T>, block: (old: T) -> T?): Pair<T, T> {
        while (true) {
            val old = getter()
            val newValue = block(old) ?: continue
            if (old === newValue || updater.compareAndSet(this, old, newValue)) return Pair(old, newValue)
        }
    }

    companion object {

        private const val ReservedLongIndex = -8

        // todo: replace with atomicfu, remove companion object
        private val State = updater(ByteBufferChannel::state)
        private val WriteOp = updater(ByteBufferChannel::writeOp)
        private val ReadOp = updater(ByteBufferChannel::readOp)
        private val Closed = updater(ByteBufferChannel::closed)
    }

    private object TerminatedLookAhead : LookAheadSuspendSession {
        override fun consumed(n: Int) {
            if (n > 0) throw IllegalStateException("Unable to mark $n bytes consumed for already terminated channel")
        }

        override fun request(skip: Int, atLeast: Int) = null

        suspend override fun awaitAtLeast(n: Int) {
        }
    }

    private class ClosedElement(val cause: Throwable?) {
        val sendException: Throwable
            get() = cause ?: ClosedWriteChannelException("The channel was closed")

        companion object {
            val EmptyCause = ClosedElement(null)
        }
    }
}

