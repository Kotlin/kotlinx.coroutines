package kotlinx.coroutines.experimental.io

import java.nio.*

interface ByteWriteChannel {
    /**
     * `true` if channel flushes automatically all pending bytes after every writeN function call.
     * If `false` then flush only happens at manual [flush] invocation or when the internal buffer is full.
     */
    val autoFlush: Boolean

    /**
     * `true` is channel has been closed so attempting to write to the channel will cause an exception
     */
    val isClosedForSend: Boolean

    /**
     * Byte order to be used for [writeShort], [writeInt], [writeLong], [writeFloat] and [writeDouble] operations.
     */
    var writeByteOrder: ByteOrder

    /**
     * Writes as much as possible and only suspends if buffer is full
     */
    suspend fun writeLazy(src: ByteArray, offset: Int, length: Int): Int

    suspend fun writeLazy(src: ByteBuffer): Int

    /**
     * Writes as much as possible and only suspends if buffer is full
     */
    suspend fun writeLazy(src: ByteArray) = writeLazy(src, 0, src.size)

    /**
     * Writes all [src] bytes and suspends until all bytes written. Causes flush if buffer filled up or when [autoFlush]
     * Crashes if channel get closed while writing.
     */
    suspend fun writeFully(src: ByteArray, offset: Int, length: Int)

    suspend fun writeFully(src: ByteBuffer)

    suspend fun writeFully(src: ByteArray) = writeFully(src, 0, src.size)

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
     * closes channel with specified [cause]. If no cause specified then then channel will be closed "normally":
     * all subsequent write operations will fail with
     * [kotlinx.coroutines.experimental.channels.ClosedSendChannelException] or with specified [cause]
     * all subsequent read operations will fail with [cause] if not null
     * if no cause provided then subsequent read operations may complete successfully or fail if end of stream
     * reached unexpectedly.
     * Flushes all pending write bytes (via [flush] function).
     * May be called at any time in any thread.
     * Closes the channel and returns `true` at first invocation
     * and does nothing returning `false` for all subsequent invocations ([cause] will be ignored in this case)
     */
    fun close(cause: Throwable? = null): Boolean

    /**
     * Flushes all pending write bytes making them available for read. Could be invoked in any thread at any time.
     * Does nothing if invoked after channel has been closed.
     */
    fun flush()
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

suspend fun ByteWriteChannel.writeStringUtf8(s: String) {
    val bytes = Charsets.UTF_8.encode(s)
    writeFully(bytes.array())
}

suspend fun ByteWriteChannel.writeBoolean(b: Boolean) {
    writeByte(if (b) 1 else 0)
}

/**
 * Writes UTF16 character
 */
suspend fun ByteBufferChannel.writeChar(ch: Char) {
    writeShort(ch.toInt())
}