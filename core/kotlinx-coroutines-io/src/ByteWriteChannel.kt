package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.packet.*
import kotlinx.coroutines.experimental.io.packet.ByteReadPacket
import kotlinx.io.core.*
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
     * An closure cause exception or `null` if closed successfully or not yet closed
     */
    public val closedCause: Throwable?

    /**
     * Writes as much as possible and only suspends if buffer is full
     */
    suspend fun writeAvailable(src: ByteArray, offset: Int, length: Int): Int
    suspend fun writeAvailable(src: ByteArray) = writeAvailable(src, 0, src.size)
    suspend fun writeAvailable(src: ByteBuffer): Int
    suspend fun writeAvailable(src: BufferView): Int

    /**
     * Writes all [src] bytes and suspends until all bytes written. Causes flush if buffer filled up or when [autoFlush]
     * Crashes if channel get closed while writing.
     */
    suspend fun writeFully(src: ByteArray, offset: Int, length: Int)
    suspend fun writeFully(src: ByteArray) = writeFully(src, 0, src.size)
    suspend fun writeFully(src: ByteBuffer)
    suspend fun writeFully(src: BufferView)

    /**
     * Invokes [block] when it will be possible to write at least [min] bytes
     * providing byte buffer to it so lambda can write to the buffer
     * up to [ByteBuffer.remaining] bytes. If there are no [min] bytes spaces available then the invocation could
     * suspend until the requirement will be met.
     *
     * Warning: it is not guaranteed that all of remaining bytes will be represented as a single byte buffer
     * eg: it could be 4 bytes available for write but the provided byte buffer could have only 2 remaining bytes:
     * in this case you have to invoke write again (with decreased [min] accordingly).
     *
     * @param min amount of bytes available for write, should be positive
     * @param block to be invoked when at least [min] bytes free capacity available
     */
    suspend fun write(min: Int = 1, block: (ByteBuffer) -> Unit)

    /**
     * Invokes [block] for every free buffer until it return `false`. It will also suspend every time when no free
     * space available for write.
     *
     * @param block to be invoked when there is free space available for write
     */
    suspend fun writeWhile(block: (ByteBuffer) -> Boolean)

    suspend fun writeSuspendSession(visitor: suspend WriterSuspendSession.() -> Unit)

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
     *
     * Please note that if the channel has been closed with cause and it has been provided by [reader] or [writer]
     * coroutine then the corresponding coroutine will be cancelled with [cause]. If no [cause] provided then no
     * cancellation will be propagated.
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
    return writeShort((s and 0xffff).toShort())
}

suspend fun ByteWriteChannel.writeByte(b: Int) {
    return writeByte((b and 0xff).toByte())
}

suspend fun ByteWriteChannel.writeInt(i: Long) {
    return writeInt(i.toInt())
}

suspend fun ByteWriteChannel.writeStringUtf8(s: CharSequence) {
    val packet = buildPacket {
        writeStringUtf8(s)
    }

    return writePacket(packet)
}

suspend fun ByteWriteChannel.writeStringUtf8(s: CharBuffer) {
    val packet = buildPacket {
        writeStringUtf8(s)
    }

    return writePacket(packet)
}

suspend fun ByteWriteChannel.writeStringUtf8(s: String) {
    val packet = buildPacket {
        writeStringUtf8(s)
    }

    return writePacket(packet)
}

suspend fun ByteWriteChannel.writeBoolean(b: Boolean) {
    return writeByte(if (b) 1 else 0)
}

/**
 * Writes UTF16 character
 */
suspend fun ByteWriteChannel.writeChar(ch: Char) {
    return writeShort(ch.toInt())
}

inline suspend fun ByteWriteChannel.writePacket(headerSizeHint: Int = 0, builder: ByteWritePacket.() -> Unit) {
    return writePacket(buildPacket(headerSizeHint, builder))
}

suspend fun ByteWriteChannel.writePacketSuspend(builder: suspend ByteWritePacket.() -> Unit) {
    return writePacket(buildPacket { builder() })
}

/**
 * Indicates attempt to write on [isClosedForWrite][ByteWriteChannel.isClosedForWrite] channel
 * that was closed without a cause. A _failed_ channel rethrows the original [close][ByteWriteChannel.close] cause
 * exception on send attempts.
 */
public class ClosedWriteChannelException(message: String?) : CancellationException(message)