@file:Suppress("UsePropertyAccessSyntax") // for ByteBuffer.getShort/getInt/etc

package kotlinx.coroutines.experimental.io

import kotlinx.atomicfu.*
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
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

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
    private var joining: JoiningState? = null

    @Volatile
    private var readOp: Continuation<Boolean>? = null

    @Volatile
    private var writeOp: Continuation<Unit>? = null

    private var readPosition = 0
    private var writePosition = 0

    @Volatile
    private var attachedJob: Job? = null

    internal fun attachJob(job: Job) {
        attachedJob?.cancel()
        attachedJob = job
        job.invokeOnCompletion(onCancelling = true) { cause ->
            attachedJob = null
            if (cause != null) cancel(cause)
        }
    }

    override var readByteOrder: ByteOrder = ByteOrder.BIG_ENDIAN
    override var writeByteOrder: ByteOrder = ByteOrder.BIG_ENDIAN
        set(newOrder) {
            if (field != newOrder) {
                field = newOrder
                joining?.delegatedTo?.writeByteOrder = newOrder
            }
        }

    override val availableForRead: Int
        get() = state.capacity.availableForRead

    override val availableForWrite: Int
        get() = state.capacity.availableForWrite

    override val isClosedForRead: Boolean
        get() = state === ReadWriteBufferState.Terminated && closed != null

    override val isClosedForWrite: Boolean
        get() = closed != null

    @Volatile
    override var totalBytesRead: Long = 0L
        private set

    @Volatile
    override var totalBytesWritten: Long = 0L
        private set

    override val closedCause: Throwable?
        get() = closed?.cause

    override fun close(cause: Throwable?): Boolean {
        if (closed != null) return false
        val newClosed = if (cause == null) ClosedElement.EmptyCause else ClosedElement(cause)
        state.capacity.flush()
        if (!Closed.compareAndSet(this, null, newClosed)) return false
        state.capacity.flush()
        if (state.capacity.isEmpty() || cause != null) tryTerminate()
        resumeClosed(cause)

        if (state === ReadWriteBufferState.Terminated) {
            joining?.let { ensureClosedJoined(it) }
        }

        if (cause != null) attachedJob?.cancel(cause)
//        readSuspendContinuationCache.close()
//        writeSuspendContinuationCache.close()

        return true
    }

    override fun cancel(cause: Throwable?): Boolean {
        return close(cause ?: CancellationException("Channel has been cancelled"))
    }

    private fun flushImpl(minReadSize: Int, minWriteSize: Int) {
        joining?.delegatedTo?.flush()

        val avw: Int
        val avr: Int

        while (true) {
            val s = state
            if (s === ReadWriteBufferState.Terminated) return
            s.capacity.flush()
            if (s === state) {
                avw = s.capacity.availableForWrite
                avr = s.capacity.availableForRead
                break
            }
        }

        if (avr >= minReadSize) resumeReadOp()
        val joining = joining
        if (avw >= minWriteSize && (joining == null || state === ReadWriteBufferState.Terminated)) resumeWriteOp()
    }

    override fun flush() {
        flushImpl(1, 1)
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
        writeOp?.let { existing ->
            throw IllegalStateException("Write operation is already in progress: $existing")
        }

        var _allocated: ReadWriteBufferState.Initial? = null
        var old: ReadWriteBufferState? = null

        val newState = updateStateAndGet { state ->
            old = state
            when {
                joining != null -> {
                    _allocated?.let { releaseBuffer(it) }
                    return null
                }
                closed != null -> {
                    _allocated?.let { releaseBuffer(it) }
                    throw closed!!.sendException
                }
                state === ReadWriteBufferState.IdleEmpty -> {
                    val allocated = _allocated ?: newBuffer().also { _allocated = it }
                    allocated.startWriting()
                }
                state === ReadWriteBufferState.Terminated -> {
                    _allocated?.let { releaseBuffer(it) }
                    if (joining != null) return null
                    throw closed!!.sendException
                }
                else -> state.startWriting()
            }
        }

        if (closed != null) {
            restoreStateAfterWrite()
            tryTerminate()

            throw closed!!.sendException
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

        val newState = updateStateAndGet {
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
        val newState = updateStateAndGet { state ->
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

        val newState = updateStateAndGet { state ->
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
        } else {
            if (newState is ReadWriteBufferState.IdleNonEmpty && newState.capacity.isEmpty()) {
                if (newState.capacity.tryLockForRelease() && State.compareAndSet(this, newState, ReadWriteBufferState.IdleEmpty)) {
                    newState.capacity.resetForWrite()
                    releaseBuffer(newState.initial)
                    resumeWriteOp()
                }
            }
        }
    }

    private fun setupDelegateTo(delegate: ByteBufferChannel, delegateClose: Boolean, delegateFlush: Boolean): JoiningState {
        require(this !== delegate)

        val joined = JoiningState(delegate, delegateClose, delegateFlush)
        delegate.writeByteOrder = writeByteOrder
        this.joining = joined

        val alreadyClosed = closed
        if (alreadyClosed != null) {
            if (alreadyClosed.cause != null) delegate.close(alreadyClosed.cause)
            else if (delegateClose && state === ReadWriteBufferState.Terminated) delegate.close()
            else if (delegateFlush) delegate.flush()
        } else {
            flush()
        }

        return joined
    }

    private fun tryCompleteJoining(joined: JoiningState): Boolean {
        if (!tryReleaseBuffer(true)) return false
        ensureClosedJoined(joined)

        resumeReadOp { IllegalStateException("Joining is in progress") }
        resumeWriteOp() // here we don't resume it with exception because it should resume and delegate writing

        return true
    }

    private fun tryTerminate(): Boolean {
        if (closed == null) return false

        if (!tryReleaseBuffer(false)) return false

        joining?.let { ensureClosedJoined(it) }

        resumeReadOp()
        resumeWriteOp()

        return true
    }

    private fun tryReleaseBuffer(forceTermination: Boolean): Boolean {
        var toRelease: ReadWriteBufferState.Initial? = null

        updateStateAndGet { state ->
            toRelease?.let { buffer ->
                toRelease = null
                buffer.capacity.resetForWrite()
                resumeWriteOp()
            }
            val closed = closed

            when {
                state === ReadWriteBufferState.Terminated -> return true
                state === ReadWriteBufferState.IdleEmpty -> ReadWriteBufferState.Terminated
                closed != null && state is ReadWriteBufferState.IdleNonEmpty && (state.capacity.tryLockForRelease() || closed.cause != null) -> {
                    if (closed.cause != null) state.capacity.forceLockForRelease()
                    toRelease = state.initial
                    ReadWriteBufferState.Terminated
                }
                forceTermination && state is ReadWriteBufferState.IdleNonEmpty && state.capacity.tryLockForRelease() -> {
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

        return true
    }

    private fun ByteBuffer.carryIndex(idx: Int) = if (idx >= capacity() - reservedSize) idx - (capacity() - reservedSize) else idx

    private inline fun writing(block: ByteBufferChannel.(ByteBuffer, RingBufferCapacity) -> Unit) {
        val current = joining?.let { resolveDelegation(this, it) } ?: this
        val buffer = current.setupStateForWrite() ?: return
        val capacity = current.state.capacity
        val before = current.totalBytesWritten

        try {
            current.closed?.let { throw it.sendException }
            block(current, buffer, capacity)
        } finally {
            if (capacity.isFull() || current.autoFlush) current.flush()
            if (current !== this) {
                totalBytesWritten += current.totalBytesWritten - before
            }
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

    private fun readAsMuchAsPossible(dst: ByteBuffer): Int {
        var consumed = 0

        reading { state ->
            val buffer = this
            val bufferLimit = buffer.capacity() - reservedSize

            while (true) {
                val dstRemaining = dst.remaining()
                if (dstRemaining == 0) break

                val position = readPosition
                val bufferRemaining = bufferLimit - position

                val part = state.tryReadAtMost(minOf(bufferRemaining, dstRemaining))
                if (part == 0) break

                buffer.limit(position + part)
                buffer.position(position)
                dst.put(buffer)

                bytesRead(state, part)
                consumed += part
            }

            false
        }

        return consumed
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


    private fun readAsMuchAsPossible(dst: ByteArray, offset: Int, length: Int): Int {
        var consumed = 0

        reading { state ->
            val buffer = this
            val bufferLimit = buffer.capacity() - reservedSize

            while (true) {
                val lengthRemaining = length - consumed
                if (lengthRemaining == 0) break
                val position = readPosition
                val bufferRemaining = bufferLimit - position

                val part = state.tryReadAtMost(minOf(bufferRemaining, lengthRemaining))
                if (part == 0) break

                buffer.limit(position + part)
                buffer.position(position)
                buffer.get(dst, offset + consumed, part)

                bytesRead(state, part)
                consumed += part
            }

            false
        }

        return consumed
    }

    final override suspend fun readFully(dst: ByteArray, offset: Int, length: Int) {
        val consumed = readAsMuchAsPossible(dst, offset, length)

        if (consumed < length) {
            return readFullySuspend(dst, offset + consumed, length - consumed)
        }
    }

    final override suspend fun readFully(dst: ByteBuffer): Int {
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

    private tailrec suspend fun readFullySuspend(dst: ByteArray, offset: Int, length: Int) {
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

    final override suspend fun readPacket(size: Int, headerSizeHint: Int): ByteReadPacket {
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
            return readPacketSuspend(remaining, builder, buffer)
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

    final override suspend fun readByte(): Byte {
        var b: Byte = 0

        val rc = reading {
            if (it.tryReadExact(1)) {
                b = get()
                bytesRead(it, 1)
                true
            } else false
        }

        if (rc) {
            return b
        } else {
            return readByteSuspend()
        }
    }

    private suspend fun readByteSuspend(): Byte {
        if (!readSuspend(1)) throw ClosedReceiveChannelException("EOF: one byte required")
        return readByte()
    }

    final override suspend fun readBoolean(): Boolean {
        var b = false

        val rc = reading {
            if (it.tryReadExact(1)) {
                b = get() != 0.toByte()
                bytesRead(it, 1)
                true
            } else false
        }

        if (rc) {
            return b
        } else {
            return readBooleanSuspend()
        }
    }

    private suspend fun readBooleanSuspend(): Boolean {
        if (!readSuspend(1)) throw ClosedReceiveChannelException("EOF: one byte required")
        return readBoolean()
    }

    final override suspend fun readShort(): Short {
        var sh: Short = 0

        val rc = reading {
            if (it.tryReadExact(2)) {
                if (remaining() < 2) rollBytes(2)
                sh = getShort()
                bytesRead(it, 2)
                true
            } else false
        }

        if (rc) {
            return sh
        } else {
            return readShortSuspend()
        }
    }

    private suspend fun readShortSuspend(): Short {
        if (!readSuspend(2)) throw ClosedReceiveChannelException("EOF while byte expected")
        return readShort()
    }

    final override suspend fun readInt(): Int {
        var i = 0

        val rc = reading {
            if (it.tryReadExact(4)) {
                if (remaining() < 4) rollBytes(4)
                i = getInt()
                bytesRead(it, 4)
                true
            } else false
        }

        if (rc) {
            return i
        } else {
            return readIntSuspend()
        }
    }

    private suspend fun readIntSuspend(): Int {
        if (!readSuspend(4)) throw ClosedReceiveChannelException("EOF while an int expected")
        return readInt()
    }

    final override suspend fun readLong(): Long {
        var i = 0L

        val rc = reading {
            if (it.tryReadExact(8)) {
                if (remaining() < 8) rollBytes(8)
                i = getLong()
                bytesRead(it, 8)
                true
            } else false
        }

        if (rc) {
            return i
        } else {
            return readLongSuspend()
        }
    }

    private suspend fun readLongSuspend(): Long {
        if (!readSuspend(8)) throw ClosedReceiveChannelException("EOF while a long expected")
        return readLong()
    }

    final override suspend fun readDouble(): Double {
        var d = 0.0

        val rc = reading {
            if (it.tryReadExact(8)) {
                if (remaining() < 8) rollBytes(8)
                d = getDouble()
                bytesRead(it, 8)
                true
            } else false
        }

        if (rc) {
            return d
        } else {
            return readDoubleSuspend()
        }
    }

    private suspend fun readDoubleSuspend(): Double {
        if (!readSuspend(8)) throw ClosedReceiveChannelException("EOF while a double expected")
        return readDouble()
    }

    final override suspend fun readFloat(): Float {
        var f = 0.0f

        val rc = reading {
            if (it.tryReadExact(4)) {
                if (remaining() < 4) rollBytes(4)
                f = getFloat()
                bytesRead(it, 4)
                true
            } else false
        }

        if (rc) {
            return f
        } else {
            return readFloatSuspend()
        }
    }

    private suspend fun readFloatSuspend(): Float {
        if (!readSuspend(4)) throw ClosedReceiveChannelException("EOF while an int expected")
        return readFloat()
    }

    private fun ByteBuffer.rollBytes(n: Int) {
        val rem = remaining()

        limit(position() + n)
        for (i in 0 until n - rem) {
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

    private tailrec fun resolveDelegation(current: ByteBufferChannel, joining: JoiningState): ByteBufferChannel? {
        if (current.state === ReadWriteBufferState.Terminated) {
            val joinedTo = joining.delegatedTo
            val nextJoining = joinedTo.joining ?: return joinedTo
            return resolveDelegation(joinedTo, nextJoining)
        }

        return null
    }

    private suspend fun delegateByte(b: Byte) {
        val joined = joining!!
        if (state === ReadWriteBufferState.Terminated) return joined.delegatedTo.writeByte(b)
        return delegateSuspend(joined) { writeByte(b) }
    }

    private suspend fun delegateSuspend(joined: JoiningState, block: suspend ByteBufferChannel.() -> Unit) {
        while (true) {
            if (state === ReadWriteBufferState.Terminated) return block(joined.delegatedTo)
            writeSuspend(1)
        }
    }

    suspend override fun writeByte(b: Byte) {
        joining?.let { resolveDelegation(this, it)?.let { return it.writeByte(b) } }

        val buffer = setupStateForWrite() ?: return delegateByte(b)
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

        if (joining != null) {
            restoreStateAfterWrite()
            return delegateByte(b)
        }

        buffer.prepareBuffer(writeByteOrder, writePosition, c.availableForWrite)
        return tryWriteByte(buffer, b, c)
    }

    private suspend fun delegateShort(s: Short) {
        val joined = joining!!
        if (state === ReadWriteBufferState.Terminated) return joined.delegatedTo.writeShort(s)
        return delegateSuspend(joined) { writeShort(s) }
    }

    suspend override fun writeShort(s: Short) {
        joining?.let { resolveDelegation(this, it)?.let { return it.writeShort(s) } }

        val buffer = setupStateForWrite() ?: return delegateShort(s)
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

        if (joining != null) {
            restoreStateAfterWrite()
            return delegateShort(s)
        }

        buffer.prepareBuffer(writeByteOrder, writePosition, c.availableForWrite)
        return tryWriteShort(buffer, s, c)
    }

    private suspend fun delegateInt(i: Int) {
        val joined = joining!!
        if (state === ReadWriteBufferState.Terminated) return joined.delegatedTo.writeInt(i)
        return delegateSuspend(joined) { writeInt(i) }
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
        val buffer = setupStateForWrite()
        if (buffer == null) {
            val delegation = resolveDelegation(this, joining!!)
            @Suppress("SuspiciousEqualsCombination")
            if (delegation != null && delegation !== this) return delegation.writeInt(i)
            else return delegateSuspend(joining!!, { writeInt(i) })
        }
        val c = state.capacity
//
        if (buffer.tryWriteInt(i, c)) {
            return
        }
        return buffer.writeIntSuspend(i, c)
    }

    private tailrec suspend fun ByteBuffer.writeIntSuspend(i: Int, c: RingBufferCapacity) {
        try {
            writeSuspend(4)
        } catch (t: Throwable) {
            restoreStateAfterWrite()
            tryTerminate()
            throw t
        }

        if (joining != null) {
            restoreStateAfterWrite()
            return delegateInt(i)
        }

        prepareBuffer(writeByteOrder, writePosition, c.availableForWrite)
        if (!tryWriteInt(i, c)) {
            return writeIntSuspend(i, c)
        }
    }

    private suspend fun delegateLong(l: Long) {
        val joined = joining!!
        if (state === ReadWriteBufferState.Terminated) return joined.delegatedTo.writeLong(l)
        return delegateSuspend(joined) { writeLong(l) }
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
            if (c.isFull() || autoFlush || joining != null) flush()
            restoreStateAfterWrite()
            tryTerminate()
            return true
        }

        return false
    }

    suspend override fun writeLong(l: Long) {
        joining?.let { resolveDelegation(this, it)?.let { return it.writeLong(l) } }

        val buffer = setupStateForWrite() ?: return delegateLong(l)
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

        if (joining != null) {
            restoreStateAfterWrite()
            return delegateLong(l)
        }

        prepareBuffer(writeByteOrder, writePosition, c.availableForWrite)
        if (!tryWriteLong(l, c)) {
            return writeLongSuspend(l, c)
        }
    }

    suspend override fun writeDouble(d: Double) {
        return writeLong(java.lang.Double.doubleToRawLongBits(d))
    }

    suspend override fun writeFloat(f: Float) {
        return writeInt(java.lang.Float.floatToRawIntBits(f))
    }

    suspend override fun writeAvailable(src: ByteBuffer): Int {
        joining?.let { resolveDelegation(this, it)?.let { return it.writeAvailable(src) } }

        val copied = writeAsMuchAsPossible(src)
        if (copied > 0) return copied

        joining?.let { resolveDelegation(this, it)?.let { return it.writeAvailableSuspend(src) } }
        return writeAvailableSuspend(src)
    }

    suspend override fun writeAvailable(src: BufferView): Int {
        joining?.let { resolveDelegation(this, it)?.let { return it.writeAvailable(src) } }

        val copied = writeAsMuchAsPossible(src)
        if (copied > 0) return copied

        joining?.let { resolveDelegation(this, it)?.let { return it.writeAvailableSuspend(src) } }
        return writeAvailableSuspend(src)
    }

    private suspend fun writeAvailableSuspend(src: ByteBuffer): Int {
        writeSuspend(1) // here we don't need to restoreStateAfterWrite as write copy loop doesn't hold state

        joining?.let { resolveDelegation(this, it)?.let { return it .writeAvailableSuspend(src) } }

        return writeAvailable(src)
    }

    private suspend fun writeAvailableSuspend(src: BufferView): Int {
        writeSuspend(1)

        joining?.let { resolveDelegation(this, it)?.let { return it.writeAvailableSuspend(src) } }

        return writeAvailable(src)
    }

    suspend override fun writeFully(src: ByteBuffer) {
        joining?.let { resolveDelegation(this, it)?.let { return it.writeFully(src) } }

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
            tryWriteSuspend(1)

            joining?.let { resolveDelegation(this, it)?.let { return it.writeFully(src) } }

            writeAsMuchAsPossible(src)
        }
    }

    private suspend fun writeFullySuspend(src: BufferView) {
        while (src.canRead()) {
            tryWriteSuspend(1)

            joining?.let { resolveDelegation(this, it)?.let { return it.writeFully(src) } }

            writeAsMuchAsPossible(src)
        }
    }

    private suspend fun awaitClose() {
        if (closed != null) return
        val joined = joining

        if (joined != null) {
            return joined.awaitClose()
        } else if (closed == null) {
            error("Only works for joined")
        }
    }

    internal suspend fun joinFrom(src: ByteBufferChannel, delegateClose: Boolean, delegateFlush: Boolean) {
        if (src.closed != null && src.state === ReadWriteBufferState.Terminated) {
            if (delegateClose) close(src.closed!!.cause)
            return
        }
        closed?.let { closed ->
            if (src.closed == null) throw closed.sendException
            return
        }

        val joined = src.setupDelegateTo(this, delegateClose, delegateFlush)
        if (src.tryCompleteJoining(joined)) {
            return src.awaitClose()
        }

        return joinFromSuspend(src, delegateClose, joined)
    }

    private suspend fun joinFromSuspend(src: ByteBufferChannel, delegateClose: Boolean, joined: JoiningState) {
        copyDirect(src, Long.MAX_VALUE, joined)

        if (delegateClose && src.isClosedForRead) {
            close()
        } else {
            if (joined.delegateFlush) {
                flush()
            }
            src.awaitClose()
        }
    }

    internal suspend fun copyDirect(src: ByteBufferChannel, limit: Long, joined: JoiningState?): Long {
        if (limit == 0L) return 0L
        if (src.isClosedForRead) {
            if (joined != null) {
                check(src.tryCompleteJoining(joined))
            }
            return 0L
        }
        if (joined != null && src.tryCompleteJoining(joined)) {
            return 0L
        }

        val autoFlush = autoFlush
        val byteOrder = writeByteOrder

        try {
            var copied = 0L
            while (copied < limit) {
                writing { dstBuffer, state ->
                    while (copied < limit) {
                        var avWBefore = state.availableForWrite
                        if (avWBefore == 0) {
                            tryWriteSuspend(1)
                            if (joining != null) break
                            avWBefore = state.availableForWrite
                        }

                        dstBuffer.prepareBuffer(byteOrder, writePosition, avWBefore)

                        var partSize = 0

                        src.reading { srcState ->
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

                        if (partSize > 0) {
                            dstBuffer.bytesWritten(state, partSize)
                            copied += partSize

                            if (avWBefore - partSize == 0 || autoFlush) {
                                flush()
                            }
                        } else {
                            break
                        }
                    }
                }

                if (joined != null) {
                    if (src.tryCompleteJoining(joined)) break
                    else if (src.state.capacity.flush()) { // force flush src to read-up all the bytes
                        src.resumeWriteOp()
                        continue
                    }
                }

                if (copied >= limit) break

                flush()

                if (src.availableForRead == 0)  {
                    if (src.readSuspendImpl(1)) {
                        if (joined != null && src.tryCompleteJoining(joined)) break
                    } else if (joined == null || src.tryCompleteJoining(joined)) break
                }

                if (joining != null) {
                    tryWriteSuspend(1)
                }
            }

            if (autoFlush) {
                flush()
            }

            return copied
        } catch (t: Throwable) {
            close(t)
            throw t
        }
    }

    private fun ensureClosedJoined(joined: JoiningState) {
        val closed = closed ?: return
        this.joining = null

        if (joined.delegateClose) {
            // writing state could be if we are inside of copyDirect loop
            // so in this case we shouldn't close channel
            // otherwise few bytes could be lost
            // it will be closed later in copyDirect's finalization
            // so we only do flush
            val writing = joined.delegatedTo.state.let { it is ReadWriteBufferState.Writing || it is ReadWriteBufferState.ReadingWriting }
            if (closed.cause != null || !writing) {
                joined.delegatedTo.close(closed.cause)
            } else if (joined.delegateFlush) {
                joined.delegatedTo.flush()
            }
        } else if (joined.delegateFlush) {
            joined.delegatedTo.flush()
        }

        joined.complete()
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
        joining?.let { resolveDelegation(this, it)?.let { return it .writeFully(src, offset, length) } }

        var rem = length
        var off = offset

        while (rem > 0) {
            val s = writeAsMuchAsPossible(src, off, rem)
            if (s == 0) break

            off += s
            rem -= s
        }

        if (rem == 0) return

        return writeFullySuspend(src, off, rem)
    }

    private tailrec suspend fun writeFullySuspend(src: ByteArray, offset: Int, length: Int) {
        if (length == 0) return
        writeSuspendUnit(src, offset, length)
        val copied = writeSuspendResult
        return writeFullySuspend(src, offset + copied, length - copied)
    }

    suspend override fun writeAvailable(src: ByteArray, offset: Int, length: Int): Int {
        joining?.let { resolveDelegation(this, it)?.let { return it.writeAvailable(src, offset, length) } }

        val size = writeAsMuchAsPossible(src, offset, length)
        if (size > 0) return size
        return writeSuspend(src, offset, length)
    }

    private var writeSuspendResult: Int = 0

    private suspend fun writeSuspendUnit(src: ByteArray, offset: Int, length: Int) {
        while (true) {
            tryWriteSuspend(1)

            joining?.let { resolveDelegation(this, it)?.let { return it.writeSuspendUnit(src, offset, length) } }

            val size = writeAsMuchAsPossible(src, offset, length)
            if (size > 0) {
                writeSuspendResult = size
                return
            }
        }
    }

    private suspend fun writeSuspend(src: ByteArray, offset: Int, length: Int): Int {
        while (true) {
            tryWriteSuspend(1)

            joining?.let { resolveDelegation(this, it)?.let { return it.writeSuspend(src, offset, length) } }

            val size = writeAsMuchAsPossible(src, offset, length)
            if (size > 0) return size
        }
    }

    override suspend fun write(min: Int, block: (ByteBuffer) -> Unit) {
        require(min > 0) { "min should be positive"}

        var written = false

        writing { dst, state ->
            val locked = state.tryWriteAtLeast(min)

            if (locked > 0) {
                // here we have locked all remaining for write bytes
                // however we don't know how many bytes will be actually written
                // so later we have to return (locked - actuallyWritten) bytes back

                // it is important to lock bytes to fail concurrent tryLockForRelease
                // once we have locked some bytes, tryLockForRelease will fail so it is safe to use buffer

                val position = dst.position()
                val l = dst.limit()
                block(dst)
                if (l != dst.limit()) throw IllegalStateException("buffer limit modified")

                val actuallyWritten = dst.position() - position
                if (actuallyWritten < 0) throw IllegalStateException("position has been moved backward: pushback is not supported")

                dst.bytesWritten(state, actuallyWritten)

                if (actuallyWritten < locked) {
                    state.completeRead(locked - actuallyWritten) // return back extra bytes (see note above)
                    // we use completeRead in spite of that it is write block
                    // we don't need to resume write as we are already in writing block
                }

                written = true
            }
        }

        if (!written) {
            return writeBlockSuspend(min, block)
        }
    }

    private suspend fun writeBlockSuspend(min: Int, block: (ByteBuffer) -> Unit) {
        writeSuspend(min)
        joining?.let { resolveDelegation(this, it)?.let { return it.write(min, block) } }
        return write(min, block)
    }

    override suspend fun writeWhile(block: (ByteBuffer) -> Boolean) {
        if (!writeWhileNoSuspend(block)) return
        closed?.let { throw it.sendException }
        return writeWhileSuspend(block)
    }

    private fun writeWhileNoSuspend(block: (ByteBuffer) -> Boolean): Boolean {
        var continueWriting = true

        writing { dst, capacity ->
            continueWriting = writeWhileLoop(dst, capacity, block)
        }

        return continueWriting
    }

    private suspend fun writeWhileSuspend(block: (ByteBuffer) -> Boolean) {
        var continueWriting = true

        writing { dst, capacity ->
            while (true) {
                writeSuspend(1)
                if (joining != null) break
                if (!writeWhileLoop(dst, capacity, block)) {
                    continueWriting = false
                    break
                }
                if (closed != null) break
            }
        }

        if (!continueWriting) return
        closed?.let { throw it.sendException }
        joining?.let { return writeWhile(block) }
    }

    // it should be writing state set to use this function
    private fun writeWhileLoop(dst: ByteBuffer, capacity: RingBufferCapacity, block: (ByteBuffer) -> Boolean): Boolean {
        var continueWriting = true
        val bufferLimit = dst.capacity() - reservedSize

        while (continueWriting) {
            val locked = capacity.tryWriteAtLeast(1) // see comments in [write]
            if (locked == 0) break

            val position = writePosition
            val l = (position + locked).coerceAtMost(bufferLimit)
            dst.limit(l)
            dst.position(position)

            continueWriting = try {
                block(dst)
            } catch (t: Throwable) {
                capacity.completeRead(locked)
                throw t
            }

            if (dst.limit() != l) throw IllegalStateException("buffer limit modified")
            val actuallyWritten = dst.position() - position
            if (actuallyWritten < 0) throw IllegalStateException("position has been moved backward: pushback is not supported")

            dst.bytesWritten(capacity, actuallyWritten)
            if (actuallyWritten < locked) {
                capacity.completeRead(locked - actuallyWritten) // return back extra bytes
                // it is important to use completeRead in spite of that we are writing here
                // no need to resume read here
            }
        }

        return continueWriting
    }

    override suspend fun read(min: Int, block: (ByteBuffer) -> Unit) {
        require(min >= 0) { "min should be positive or zero" }

        val read = reading {
            val av = it.availableForRead
            if (av > 0 && av >= min) {
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
            if (isClosedForRead) return
            return readBlockSuspend(min, block)
        }
    }

    override suspend fun discard(max: Long): Long {
        require(max >= 0) { "max shouldn't be negative: $max" }

        var discarded = 0L

        reading {
            val n = it.tryReadAtMost(minOf(Int.MAX_VALUE.toLong(), max).toInt())
            bytesRead(it, n)
            discarded += n
            true
        }

        if (discarded == max || isClosedForRead) return discarded

        return discardSuspend(discarded, max)
    }

    private suspend fun discardSuspend(discarded0: Long, max: Long): Long {
        var discarded = discarded0

        while (discarded < max) {
            val rc = reading {
                val n = it.tryReadAtMost(minOf(Int.MAX_VALUE.toLong(), max - discarded).toInt())
                bytesRead(it, n)
                discarded += n

                true
            }

            if (!rc) {
                if (isClosedForRead || !readSuspend(1)) break
            }
        }

        return discarded
    }

    private suspend fun readBlockSuspend(min: Int, block: (ByteBuffer) -> Unit) {
        if (!readSuspend(min.coerceAtLeast(1))) {
            if (min > 0)
                throw EOFException("Got EOF but at least $min bytes were expected")
            else return
        }

        read(min, block)
    }

    override suspend fun writePacket(packet: ByteReadPacket) {
        joining?.let { resolveDelegation(this, it)?.let { return it.writePacket(packet) } }

        try {
            while (!packet.isEmpty) {
                if (tryWritePacketPart(packet) == 0) break
            }
        } catch (t: Throwable) {
            packet.release()
            throw t
        }

        if (packet.remaining > 0) {
            joining?.let { resolveDelegation(this, it)?.let { return it.writePacket(packet) } }
            return writePacketSuspend(packet)
        }
    }

    private suspend fun writePacketSuspend(packet: ByteReadPacket) {
        try {
            while (!packet.isEmpty) {
                writeSuspend(1)

                joining?.let { resolveDelegation(this, it)?.let { return it.writePacket(packet) } }
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
    final override suspend fun consumeEachBufferRange(visitor: (buffer: ByteBuffer, last: Boolean) -> Boolean) {
        if (consumeEachBufferRangeFast(false, visitor)) return
        return consumeEachBufferRangeSuspend(visitor)
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

    override suspend fun writeSuspendSession(visitor: suspend WriterSuspendSession.() -> Unit) {
        var locked = 0

        var current = joining?.let { resolveDelegation(this, it) } ?: this
        var byteBuffer = current.setupStateForWrite() ?: return writeSuspendSession(visitor)
        var ringBufferCapacity = current.state.capacity

        val session = object : WriterSuspendSession {
            override fun request(min: Int): ByteBuffer? {
                locked += ringBufferCapacity.tryWriteAtLeast(0)
                if (locked < min) return null
                byteBuffer.prepareBuffer(writeByteOrder, writePosition, locked)
                if (byteBuffer.remaining() < min) return null
                if (current.joining != null) return null

                return byteBuffer
            }

            override fun written(n: Int) {
                require(n >= 0)
                if (n > locked) throw IllegalStateException()
                locked -= n
                byteBuffer.bytesWritten(ringBufferCapacity, n)
            }

            override suspend fun tryAwait(n: Int) {
                val joining = current.joining
                if (joining != null) {
                    return tryAwaitJoinSwitch(n, joining)
                }

                if (locked >= n) return
                if (locked > 0) {
                    ringBufferCapacity.completeRead(locked)
                    locked = 0
                }

                return tryWriteSuspend(n)
            }

            private suspend fun tryAwaitJoinSwitch(n: Int, joining: JoiningState) {
                if (locked > 0) {
                    ringBufferCapacity.completeRead(locked)
                    locked = 0
                }
                flush()
                restoreStateAfterWrite()
                tryTerminate()

                do {
                    current.tryWriteSuspend(n)
                    current = resolveDelegation(current, joining) ?: continue
                    byteBuffer = current.setupStateForWrite() ?: continue
                    ringBufferCapacity = current.state.capacity
                } while (false)
            }
        }

        try {
            visitor(session)
        } finally {
            if (locked > 0) {
                ringBufferCapacity.completeRead(locked)
                locked = 0
            }

            current.restoreStateAfterWrite()
            current.tryTerminate()
        }
    }

    override fun consumed(n: Int) {
        require(n >= 0)

        state.let { s ->
            if (!s.capacity.tryReadExact(n)) throw IllegalStateException("Unable to consume $n bytes: not enough available bytes")
            s.readBuffer.bytesRead(s.capacity, n)
        }
    }

    final override suspend fun awaitAtLeast(n: Int): Boolean {
        if (state.capacity.availableForRead >= n) {
            if (state.idle || state is ReadWriteBufferState.Writing) setupStateForRead()
            return true
        }

        if (state.idle || state is ReadWriteBufferState.Writing) return awaitAtLeastSuspend(n)
        else if (n == 1) return readSuspendImpl(1)
        else return readSuspend(n)
    }

    private suspend fun awaitAtLeastSuspend(n: Int): Boolean {
        val rc = readSuspend(n)
        if (rc && state.idle) {
            setupStateForRead()
        }
        return rc
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
        val rc = reading {
            do {
                if (hasRemaining() || last) {
                    val rc = visitor(this, last)
                    afterBufferVisited(this, it)
                    if (!rc || (last && !hasRemaining())) return true
                } else break
            } while (true)

            last
        }

        if (!rc && closed != null) {
            visitor(EmptyByteBuffer, true)
            return true
        }

        return rc
    }

//    private suspend fun consumeEachBufferRangeSuspendLoop(visitor: RendezvousChannel<ConsumeEachBufferVisitor>) {
//        var last = false
//
//        do {
//            if (consumeEachBufferRangeFast(last, visitor)) return
//            if (last) return
//            if (!readSuspend(1)) {
//                last = true
//            }
//        } while (true)
//    }

    private suspend fun consumeEachBufferRangeSuspend(visitor: (buffer: ByteBuffer, last: Boolean) -> Boolean) {
        var last = false

        do {
            if (consumeEachBufferRangeFast(last, visitor)) return
            if (last) return
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
        ReadOp.getAndSet(this, null)?.apply {
            val closedCause = closed?.cause
            when {
                closedCause != null -> resumeWithException(closedCause)
                else -> resume(true)
            }
        }
    }

    private inline fun resumeReadOp(exception: () -> Throwable) {
        ReadOp.getAndSet(this, null)?.resumeWithException(exception())
    }

    private fun resumeWriteOp() {
        while (true) {
            val writeOp = writeOp ?: return
            val closed = closed
            if (closed == null && joining != null) {
                val state = state
                if (state is ReadWriteBufferState.Writing || state is ReadWriteBufferState.ReadingWriting) {
                } else if (state !== ReadWriteBufferState.Terminated) return
            }
            if (WriteOp.compareAndSet(this, writeOp, null)) {
                if (closed == null) writeOp.resume(Unit) else writeOp.resumeWithException(closed.sendException)
                return
            }
        }
    }

    private fun resumeClosed(cause: Throwable?) {
        ReadOp.getAndSet(this, null)?.let { c ->
            if (cause != null)
                c.resumeWithException(cause)
            else
                c.resume(state.capacity.availableForRead > 0)
        }

        WriteOp.getAndSet(this, null)?.resumeWithException(cause ?:
            ClosedWriteChannelException(DEFAULT_CLOSE_MESSAGE))
    }

    private suspend fun readSuspend(size: Int): Boolean {
        val capacity = state.capacity
        if (capacity.availableForRead >= size) return true

        closed?.let { c ->
            if (c.cause != null) throw c.cause
            val afterCapacity = state.capacity
            val result = afterCapacity.flush() && afterCapacity.availableForRead >= size
            if (readOp != null) throw IllegalStateException("Read operation is already in progress")
            return result
        }

        if (size == 1) return readSuspendImpl(1)
        return readSuspendLoop(size)
    }

    private tailrec suspend fun readSuspendLoop(size: Int): Boolean {
        val capacity = state.capacity
        if (capacity.availableForRead >= size) return true

        closed?.let { c ->
            if (c.cause != null) throw c.cause
            val afterCapacity = state.capacity
            val result = afterCapacity.flush() && afterCapacity.availableForRead >= size
            if (readOp != null) throw IllegalStateException("Read operation is already in progress")
            return result
        }

        if (!readSuspendImpl(size)) return false

        return readSuspendLoop(size)
    }

    private val readSuspendContinuationCache = MutableDelegateContinuation<Boolean>()

    @Suppress("NOTHING_TO_INLINE")
    private inline fun readSuspendPredicate(size: Int): Boolean {
        val state = state

        if (state.capacity.availableForRead >= size) return false
        if (joining != null && writeOp != null &&
                (state === ReadWriteBufferState.IdleEmpty || state is ReadWriteBufferState.IdleNonEmpty)) return false

        return true
    }

    private fun suspensionForSize(size: Int, c: Continuation<Boolean>): Any {
        do {
            if (!readSuspendPredicate(size)) {
                c.resume(true)
                break
            }

            closed?.let {
                if (it.cause != null) {
                    c.resumeWithException(it.cause)
                } else {
                    c.resume(state.capacity.flush() && state.capacity.availableForRead >= size)
                }
                return COROUTINE_SUSPENDED
            }
        } while (!setContinuation({ readOp }, ReadOp, c, { closed == null && readSuspendPredicate(size) }))

        return COROUTINE_SUSPENDED
    }

    private suspend fun readSuspendImpl(size: Int): Boolean {
        if (!readSuspendPredicate(size)) return true

        return suspendCoroutineOrReturn { raw ->
            val c = readSuspendContinuationCache
            suspensionForSize(size, c)
            c.swap(raw)
        }
    }

    private fun shouldResumeReadOp() = joining != null &&
            (state === ReadWriteBufferState.IdleEmpty || state is ReadWriteBufferState.IdleNonEmpty)

    private fun writeSuspendPredicate(size: Int): Boolean {
        val joined = joining
        val state = state
        val closed = closed

        return when {
            closed != null -> false
            joined == null -> state.capacity.availableForWrite < size && state !== ReadWriteBufferState.IdleEmpty
            else -> state !== ReadWriteBufferState.Terminated && state !is ReadWriteBufferState.Writing && state !is ReadWriteBufferState.ReadingWriting
        }
    }

    private val writeSuspendContinuationCache = MutableDelegateContinuation<Unit>()
    @Volatile
    private var writeSuspensionSize: Int = 0
    private val writeSuspension = { c: Continuation<Unit> ->
        val size = writeSuspensionSize

        do {
            closed?.sendException?.let { throw it }
            if (!writeSuspendPredicate(size)) {
                c.resume(Unit)
                break
            }
        } while (!setContinuation({ writeOp }, WriteOp, c, { writeSuspendPredicate(size) }))

        flushImpl(1, minWriteSize = size)

        if (shouldResumeReadOp()) {
            resumeReadOp()
        }

        COROUTINE_SUSPENDED
    }

    private suspend fun tryWriteSuspend(size: Int) {
        if (!writeSuspendPredicate(size)) {
            closed?.sendException?.let { throw it }
            return
        }

        writeSuspensionSize = size
        if (attachedJob != null) {
            return suspendCoroutineOrReturn(writeSuspension)
        }

        return suspendCoroutineOrReturn { raw ->
            val c = writeSuspendContinuationCache
            writeSuspension(c)
            c.swap(raw)
        }
    }

    private suspend fun writeSuspend(size: Int) {
        while (writeSuspendPredicate(size)) {
            suspendCancellableCoroutine<Unit>(holdCancellability = true) { c ->
                do {
                    closed?.sendException?.let { throw it }
                    if (!writeSuspendPredicate(size)) {
                        c.resume(Unit)
                        break
                    }
                } while (!setContinuation({ writeOp }, WriteOp, c, { writeSuspendPredicate(size) }))

                flushImpl(1, minWriteSize = size)

                if (shouldResumeReadOp()) {
                    resumeReadOp()
                }
            }
        }

        closed?.sendException?.let { throw it }
    }

    private inline fun <T, C : Continuation<T>> setContinuation(getter: () -> C?, updater: AtomicReferenceFieldUpdater<ByteBufferChannel, C?>, continuation: C, predicate: () -> Boolean): Boolean {
        while (true) {
            val current = getter()
            if (current != null) throw IllegalStateException("Operation is already in progress")

            if (!predicate()) {
                return false
            }

            if (updater.compareAndSet(this, null, continuation)) {
                if (predicate() || !updater.compareAndSet(this, continuation, null)) {
                    if (attachedJob == null && continuation is CancellableContinuation<*>) {
                        continuation.initCancellability()
                    }
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

    private inline fun updateStateAndGet(block: (ReadWriteBufferState) -> ReadWriteBufferState?): ReadWriteBufferState {
        val updater = State
        while (true) {
            val old = state
            val newState = block(old) ?: continue
            if (old === newState || updater.compareAndSet(this, old, newState)) return newState
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

        suspend override fun awaitAtLeast(n: Int): Boolean {
            return false
        }
    }

    private class ClosedElement(val cause: Throwable?) {
        val sendException: Throwable
            get() = cause ?: ClosedWriteChannelException("The channel was closed")

        companion object {
            val EmptyCause = ClosedElement(null)
        }
    }

    internal class JoiningState(val delegatedTo: ByteBufferChannel, val delegateClose: Boolean, val delegateFlush: Boolean) {
        private val _closeWaitJob = atomic<Job?>(null)
        private val closed = atomic(0)

        private val closeWaitJob: Job
            get() {
                while (true) {
                    val current = _closeWaitJob.value
                    if (current != null) return current
                    val newJob = Job()
                    if (_closeWaitJob.compareAndSet(null, newJob)) {
                        if (closed.value == 1) newJob.cancel()
                        return newJob
                    }
                }
            }

        fun complete() {
            closed.value = 1
            _closeWaitJob.getAndSet(null)?.cancel()
        }

        suspend fun awaitClose() {
            if (closed.value == 1) return
            return closeWaitJob.join()
        }
    }
}

