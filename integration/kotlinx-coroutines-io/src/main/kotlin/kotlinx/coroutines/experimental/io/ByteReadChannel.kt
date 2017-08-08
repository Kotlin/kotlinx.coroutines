package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.packet.*
import java.nio.*

interface ByteReadChannel {
    val remaining: Int

    /**
     * true if the channel is closed and no remaining bytes available for read
     */
    val isClosedForReceive: Boolean

    /**
     * Byte order that is applied when multibyte read operations invoked such as [readShort], [readInt], [readLong],
     * [readFloat] and [readDouble].
     */
    var readByteOrder: ByteOrder

    /**
     * Reads as much as possible to [dst] buffer and suspends if no bytes available
     * @return number of bytes were read or `-1` if the channel has been closed
     */
    suspend fun readLazy(dst: ByteArray, offset: Int, length: Int): Int
    suspend fun readLazy(dst: ByteBuffer): Int
    suspend fun readLazy(dst: ByteArray) = readLazy(dst, 0, dst.size)

    /**
     * Reads all [length] bytes to [dst] buffer or fails if channel has been closed.
     * Suspends if not enough bytes available.
     */
    suspend fun readFully(dst: ByteArray, offset: Int, length: Int)
    suspend fun readFully(dst: ByteBuffer): Int
    suspend fun readFully(dst: ByteArray) = readFully(dst, 0, dst.size)

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
     * Reads an unsigned int number (suspending if not enough bytes available) or fails if channel has been closed
     * and not enough bytes.
     */
    suspend fun readUInt(): Long

    /**
     * Reads an unsigned short number (suspending if not enough bytes available) or fails if channel has been closed
     * and not enough bytes.
     */
    suspend fun readUShort(): Int

    /**
     * Reads an unsigned byte (suspending if not enough bytes available) or fails if channel has been closed
     * and not enough bytes.
     */
    suspend fun readUByte(): Short

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