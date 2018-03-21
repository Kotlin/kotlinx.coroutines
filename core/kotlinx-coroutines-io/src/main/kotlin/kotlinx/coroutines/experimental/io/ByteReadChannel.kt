package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.internal.*
import kotlinx.coroutines.experimental.io.packet.*
import kotlinx.coroutines.experimental.io.packet.ByteReadPacket
import kotlinx.io.core.*

/**
 * Channel for asynchronous reading of sequences of bytes.
 * This is a **single-reader channel**.
 *
 * Operations on this channel cannot be invoked concurrently.
 */
public interface ByteReadChannel {
    /**
     * Returns number of bytes that can be read without suspension. Read operations do no suspend and return
     * immediately when this number is at least the number of bytes requested for read.
     */
    public val availableForRead: Int

    /**
     * Returns `true` if the channel is closed and no remaining bytes are available for read.
     * It implies that [availableForRead] is zero.
     */
    public val isClosedForRead: Boolean

    public val isClosedForWrite: Boolean

    /**
     * Byte order that is used for multi-byte read operations
     * (such as [readShort], [readInt], [readLong], [readFloat], and [readDouble]).
     */
    public var readByteOrder: ByteOrder

    /**
     * Number of bytes read from the channel.
     * It is not guaranteed to be atomic so could be updated in the middle of long running read operation.
     */
    public val totalBytesRead: Long

    /**
     * Reads all available bytes to [dst] buffer and returns immediately or suspends if no bytes available
     * @return number of bytes were read or `-1` if the channel has been closed
     */
    suspend fun readAvailable(dst: ByteArray, offset: Int, length: Int): Int
    suspend fun readAvailable(dst: ByteArray) = readAvailable(dst, 0, dst.size)
    suspend fun readAvailable(dst: ByteBuffer): Int
    suspend fun readAvailable(dst: BufferView): Int

    /**
     * Reads all [length] bytes to [dst] buffer or fails if channel has been closed.
     * Suspends if not enough bytes available.
     */
    suspend fun readFully(dst: ByteArray, offset: Int, length: Int)
    suspend fun readFully(dst: ByteArray) = readFully(dst, 0, dst.size)
    suspend fun readFully(dst: ByteBuffer): Int

    /**
     * Reads the specified amount of bytes and makes a byte packet from them. Fails if channel has been closed
     * and not enough bytes available. Accepts [headerSizeHint] to be provided, see [WritePacket].
     */
    suspend fun readPacket(size: Int, headerSizeHint: Int = 0): ByteReadPacket

    /**
     * Reads a long number (suspending if not enough bytes available) or fails if channel has been closed
     * and not enough bytes.
     */
    suspend fun readLong(): Long

    /**
     * Reads an int number (suspending if not enough bytes available) or fails if channel has been closed
     * and not enough bytes.
     */
    suspend fun readInt(): Int

    /**
     * Reads a short number (suspending if not enough bytes available) or fails if channel has been closed
     * and not enough bytes.
     */
    suspend fun readShort(): Short

    /**
     * Reads a byte (suspending if no bytes available yet) or fails if channel has been closed
     * and not enough bytes.
     */
    suspend fun readByte(): Byte

    /**
     * Reads a boolean value (suspending if no bytes available yet) or fails if channel has been closed
     * and not enough bytes.
     */
    suspend fun readBoolean(): Boolean

    /**
     * Reads double number (suspending if not enough bytes available) or fails if channel has been closed
     * and not enough bytes.
     */
    suspend fun readDouble(): Double

    /**
     * Reads float number (suspending if not enough bytes available) or fails if channel has been closed
     * and not enough bytes.
     */
    suspend fun readFloat(): Float

    /**
     * For every available bytes range invokes [visitor] function until it return false or end of stream encountered
     */
    suspend fun consumeEachBufferRange(visitor: ConsumeEachBufferVisitor)

    fun <R> lookAhead(visitor: LookAheadSession.() -> R): R
    suspend fun <R> lookAheadSuspend(visitor: suspend LookAheadSuspendSession.() -> R): R

    /**
     * Reads a line of UTF-8 characters to the specified [out] buffer up to [limit] characters.
     * Supports both CR-LF and LF line endings.
     * Throws an exception if the specified [limit] has been exceeded.
     *
     * @return `true` if line has been read (possibly empty) or `false` if channel has been closed
     * and no characters were read.
     */
    suspend fun <A : Appendable> readUTF8LineTo(out: A, limit: Int = Int.MAX_VALUE): Boolean

    /**
     * Invokes [block] when it will be possible to read at least [min] bytes
     * providing byte buffer to it so lambda can read from the buffer
     * up to [ByteBuffer.remaining] bytes. If there are no [min] bytes available then the invocation could
     * suspend until the requirement will be met.
     *
     * If [min] is zero then the invocation will suspend until at least one byte available.
     *
     * Warning: it is not guaranteed that all of remaining bytes will be represented as a single byte buffer
     * eg: it could be 4 bytes available for read but the provided byte buffer could have only 2 remaining bytes:
     * in this case you have to invoke read again (with decreased [min] accordingly).
     *
     * It will fail with [EOFException] if not enough bytes ([availableForRead] < [min]) available
     * in the channel after it is closed.
     *
     * [block] lambda should modify buffer's position accordingly. It also could temporarily modify limit however
     * it should restore it before return. It is not recommended to access any bytes of the buffer outside of the
     * provided byte range [position(); limit()) as there could be any garbage or incomplete data.
     *
     * @param min amount of bytes available for read, should be positive or zero
     * @param block to be invoked when at least [min] bytes available for read
     */
    suspend fun read(min: Int = 1, block: (ByteBuffer) -> Unit)

    /**
     * Close channel with optional [cause] cancellation. Unlike [ByteWriteChannel.close] that could close channel
     * normally, cancel does always close with error so any operations on this channel will always fail
     * and all suspensions will be resumed with exception.
     *
     * Please note that if the channel has been provided by [reader] or [writer] then the corresponding owning
     * coroutine will be cancelled as well
     *
     * @see ByteWriteChannel.close
     */
    fun cancel(cause: Throwable? = null): Boolean

    /**
     * Discard up to [max] bytes
     *
     * @return number of bytes were discarded
     */
    suspend fun discard(max: Long = Long.MAX_VALUE): Long
}

typealias ConsumeEachBufferVisitor = (buffer: java.nio.ByteBuffer, last: Boolean) -> Boolean

suspend fun ByteReadChannel.joinTo(dst: ByteWriteChannel, closeOnEnd: Boolean, flushOnEnd: Boolean = true) {
    require(dst !== this)

    if (this is ByteBufferChannel && dst is ByteBufferChannel) {
        return dst.joinFrom(this, closeOnEnd, flushOnEnd)
    }

    return joinToImplSuspend(dst, closeOnEnd, flushOnEnd)
}

private suspend fun ByteReadChannel.joinToImplSuspend(dst: ByteWriteChannel, close: Boolean, flush: Boolean) {
    copyToImpl(dst, Long.MAX_VALUE)
    if (close) {
        dst.close()
    } else if (flush) {
        dst.flush()
    }
}

/**
 * Reads up to [limit] bytes from receiver channel and writes them to [dst] channel.
 * Closes [dst] channel if fails to read or write with cause exception.
 * @return a number of copied bytes
 */
suspend fun ByteReadChannel.copyTo(dst: ByteWriteChannel, limit: Long = Long.MAX_VALUE): Long {
    require(this !== dst)
    require(limit >= 0L)

    if (this is ByteBufferChannel && dst is ByteBufferChannel) {
        return dst.copyDirect(this, limit, null)
    }

    return copyToImpl(dst, limit)
}

private suspend fun ByteReadChannel.copyToImpl(dst: ByteWriteChannel, limit: Long): Long {
    val buffer = BufferPool.borrow()
    val dstNeedsFlush = !dst.autoFlush

    try {
        var copied = 0L

        while (true) {
            buffer.clear()

            val bufferLimit = limit - copied
            if (bufferLimit <= 0) break
            if (bufferLimit < buffer.limit()) {
                buffer.limit(bufferLimit.toInt())
            }
            val size = readAvailable(buffer)
            if (size == -1) break

            buffer.flip()
            dst.writeFully(buffer)
            copied += size

            if (dstNeedsFlush && availableForRead == 0) {
                dst.flush()
            }
        }
        return copied
    } catch (t: Throwable) {
        dst.close(t)
        throw t
    } finally {
        BufferPool.recycle(buffer)
    }
}

/**
 * Reads all the bytes from receiver channel and writes them to [dst] channel and then closes it.
 * Closes [dst] channel if fails to read or write with cause exception.
 * @return a number of copied bytes
 */
suspend fun ByteReadChannel.copyAndClose(dst: ByteWriteChannel, limit: Long = Long.MAX_VALUE): Long {
    val count = copyTo(dst, limit)
    dst.close()
    return count
}

/**
 * Reads all the bytes from receiver channel and builds a packet that is returned unless the specified [limit] exceeded.
 * It will simply stop reading and return packet of size [limit] in this case
 */
suspend fun ByteReadChannel.readRemaining(limit: Int = Int.MAX_VALUE): ByteReadPacket {
    val buffer = BufferPool.borrow()
    val packet = WritePacket()

    try {
        var copied = 0L

        while (copied < limit) {
            buffer.clear()
            if (limit - copied < buffer.limit()) {
                buffer.limit((limit - copied).toInt())
            }
            val size = readAvailable(buffer)
            if (size == -1) break

            buffer.flip()
            packet.writeFully(buffer)
            copied += size
        }

        return packet.build()
    } catch (t: Throwable) {
        packet.release()
        throw t
    } finally {
        BufferPool.recycle(buffer)
    }
}
