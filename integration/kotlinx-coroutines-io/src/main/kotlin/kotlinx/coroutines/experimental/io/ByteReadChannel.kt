package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.internal.BufferObjectPool
import kotlinx.coroutines.experimental.io.packet.ByteReadPacket

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

    /**
     * Byte order that is used for multi-byte read operations
     * (such as [readShort], [readInt], [readLong], [readFloat], and [readDouble]).
     */
    public var readByteOrder: ByteOrder

    /**
     * Reads all available bytes to [dst] buffer and returns immediately or suspends if no bytes available
     * @return number of bytes were read or `-1` if the channel has been closed
     */
    suspend fun readAvailable(dst: ByteArray, offset: Int, length: Int): Int
    suspend fun readAvailable(dst: ByteArray) = readAvailable(dst, 0, dst.size)
    suspend fun readAvailable(dst: ByteBuffer): Int

    /**
     * Reads all [length] bytes to [dst] buffer or fails if channel has been closed.
     * Suspends if not enough bytes available.
     */
    suspend fun readFully(dst: ByteArray, offset: Int, length: Int)
    suspend fun readFully(dst: ByteArray) = readFully(dst, 0, dst.size)
    suspend fun readFully(dst: ByteBuffer): Int

    /**
     * Reads the specified amount of bytes and makes a byte packet from them. Fails if channel has been closed
     * and not enough bytes available.
     */
    suspend fun readPacket(size: Int): ByteReadPacket

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

    suspend fun lookAhead(visitor: (buffer: ByteBuffer, last: Boolean) -> Boolean)

    /**
     * Reads a line of UTF-8 characters to the specified [out] buffer up to [limit] characters.
     * Supports both CR-LF and LF line endings.
     * Throws an exception if the specified [limit] has been exceeded.
     *
     * @return `true` if line has been read (possibly empty) or `false` if channel has been closed
     * and no characters were read.
     */
    suspend fun <A : Appendable> readUTF8LineTo(out: A, limit: Int = Int.MAX_VALUE): Boolean
}

suspend fun ByteReadChannel.copyAndClose(dst: ByteWriteChannel): Long {
    val o = BufferObjectPool.borrow()
    try {
        var copied = 0L
        val bb = o.backingBuffer
        bb.clear()

        while (true) {
            val size = readAvailable(bb)
            if (size == -1) break

            bb.flip()
            dst.writeFully(bb)
            copied += size
        }

        dst.close()
        return copied
    } catch (t: Throwable) {
        dst.close(t)
        throw t
    } finally {
        BufferObjectPool.recycle(o)
    }
}
