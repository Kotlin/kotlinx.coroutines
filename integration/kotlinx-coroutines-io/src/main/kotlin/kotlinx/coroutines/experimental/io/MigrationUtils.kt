package kotlinx.coroutines.experimental.io

/**
 * See [java.io.DataOutput.writeUTF]
 */
@Deprecated("Use writeStringUtf8 instead", ReplaceWith("writeStringUtf8(s)"))
suspend fun ByteBufferChannel.writeUTF(s: String) {
    writeStringUtf8(s)
}

/**
 * See [java.io.DataOutput.writeChars]
 */
suspend fun ByteBufferChannel.writeChars(s: String) {
    for (ch in s) {
        writeShort(ch.toInt())
    }
}

/**
 * See [java.io.DataOutput.writeBytes]
 */
suspend fun ByteBufferChannel.writeBytes(s: String) {
    for (ch in s) {
        writeByte(ch.toInt())
    }
}

/**
 * See [java.io.DataOutput.write]
 */
@Deprecated("Use writeFully instead", ReplaceWith("writeFully(src)"))
suspend fun ByteBufferChannel.write(src: ByteArray) = writeFully(src)

/**
 * See [java.io.DataOutput.write]
 */
@Deprecated("Use writeFully instead", ReplaceWith("writeFully(src, offset, length)"))
suspend fun ByteBufferChannel.write(src: ByteArray, offset: Int, length: Int) = writeFully(src, offset, length)
