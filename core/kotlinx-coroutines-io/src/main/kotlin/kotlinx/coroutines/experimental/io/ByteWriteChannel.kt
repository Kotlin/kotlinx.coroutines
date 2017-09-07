package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.packet.*
import java.nio.ByteBuffer
import java.nio.CharBuffer
import java.util.concurrent.CancellationException

/**
 * Channel for asynchronous writing of sequences of bytes.
 * This is a **single-writer channel**.
 *
 * Operations on this channel cannot be invoked concurrently, unless explicitly specified otherwise
 * in description. Exceptions are [close] and [flush].
 */
public interface ByteWriteChannel {
    /**
     * Returns number of bytes that can be written without suspension. Write operations do no suspend and return
     * immediately when this number is at least the number of bytes requested for write.
     */
    public val availableForWrite: Int

    /**
     * Returns `true` is channel has been closed and attempting to write to the channel will cause an exception.
     */
    public val isClosedForWrite: Boolean

    /**
     * Returns `true` if channel flushes automatically all pending bytes after every write function call.
     * If `false` then flush only happens at manual [flush] invocation or when the buffer is full.
     */
    public val autoFlush: Boolean

    /**
     * Byte order that is used for multi-byte write operations
     * (such as [writeShort], [writeInt], [writeLong], [writeFloat], and [writeDouble]).
     */
    public var writeByteOrder: ByteOrder

    /**
     * Number of bytes written to the channel.
     * It is not guaranteed to be atomic so could be updated in the middle of write operation.
     */
    public val totalBytesWritten: Long

    /**
     * Writes as much as possible and only suspends if buffer is full
     */
    suspend fun writeAvailable(src: ByteArray, offset: Int, length: Int): Int
    suspend fun writeAvailable(src: ByteArray) = writeAvailable(src, 0, src.size)
    suspend fun writeAvailable(src: ByteBuffer): Int

    /**
     * Writes all [src] bytes and suspends until all bytes written. Causes flush if buffer filled up or when [autoFlush]
     * Crashes if channel get closed while writing.
     */
    suspend fun writeFully(src: ByteArray, offset: Int, length: Int)
    suspend fun writeFully(src: ByteArray) = writeFully(src, 0, src.size)
    suspend fun writeFully(src: ByteBuffer)

    /**
     * Writes a [packet] fully or fails if channel get closed before the whole packet has been written
     */
    suspend fun writePacket(packet: ByteReadPacket)
    /**
     * Writes long number and suspends until written.
     * Crashes if channel get closed while writing.
     */
    suspend fun writeLong(l: Long)

    /**
     * Writes int number and suspends until written.
     * Crashes if channel get closed while writing.
     */
    suspend fun writeInt(i: Int)

    /**
     * Writes short number and suspends until written.
     * Crashes if channel get closed while writing.
     */
    suspend fun writeShort(s: Short)

    /**
     * Writes byte and suspends until written.
     * Crashes if channel get closed while writing.
     */
    suspend fun writeByte(b: Byte)

    /**
     * Writes double number and suspends until written.
     * Crashes if channel get closed while writing.
     */
    suspend fun writeDouble(d: Double)

    /**
     * Writes float number and suspends until written.
     * Crashes if channel get closed while writing.
     */
    suspend fun writeFloat(f: Float)

    /**
     * Closes this channel with an optional exceptional [cause].
     * It flushes all pending write bytes (via [flush]).
     * This is an idempotent operation -- repeated invocations of this function have no effect and return `false`.
     *
     * A channel that was closed without a [cause], is considered to be _closed normally_.
     * A channel that was closed with non-null [cause] is called a _failed channel_. Attempts to read or
     * write on a failed channel throw this cause exception.
     *
     * After invocation of this operation [isClosedForWrite] starts returning `true` and
     * all subsequent write operations throw [ClosedWriteChannelException] or the specified [cause].
     * However, [isClosedForRead][ByteReadChannel.isClosedForRead] on the side of [ByteReadChannel]
     * starts returning `true` only after all written bytes have been read.
     */
    public fun close(cause: Throwable? = null): Boolean

    /**
     * Flushes all pending write bytes making them available for read.
     *
     * This function is thread-safe and can be invoked in any thread at any time.
     * It does nothing when invoked on a closed channel.
     */
    public fun flush()
}

suspend fun ByteWriteChannel.writeShort(s: Int) {
    writeShort((s and 0xffff).toShort())
}

suspend fun ByteWriteChannel.writeByte(b: Int) {
    writeByte((b and 0xff).toByte())
}

suspend fun ByteWriteChannel.writeInt(i: Long) {
    writeInt(i.toInt())
}

suspend fun ByteWriteChannel.writeStringUtf8(s: CharSequence) {
    val packet = buildPacket {
        writeStringUtf8(s)
    }
    writePacket(packet)
}

suspend fun ByteWriteChannel.writeStringUtf8(s: CharBuffer) {
    val packet = buildPacket {
        writeStringUtf8(s)
    }
    writePacket(packet)
}

suspend fun ByteWriteChannel.writeStringUtf8(s: String) {
    val packet = buildPacket {
        writeStringUtf8(s)
    }
    writePacket(packet)
}

suspend fun ByteWriteChannel.writeBoolean(b: Boolean) {
    writeByte(if (b) 1 else 0)
}

/**
 * Writes UTF16 character
 */
suspend fun ByteWriteChannel.writeChar(ch: Char) {
    writeShort(ch.toInt())
}

inline suspend fun ByteWriteChannel.writePacket(builder: ByteWritePacket.() -> Unit) {
    writePacket(buildPacket(builder))
}

suspend fun ByteWriteChannel.writePacketSuspend(builder: suspend ByteWritePacket.() -> Unit) {
    writePacket(buildPacket { builder() })
}

class ClosedWriteChannelException(message: String?) : CancellationException(message)