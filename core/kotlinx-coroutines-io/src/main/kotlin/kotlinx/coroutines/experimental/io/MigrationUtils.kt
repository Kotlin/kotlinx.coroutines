package kotlinx.coroutines.experimental.io

/**
 * See [java.io.DataOutput.writeUTF]
 */
@Deprecated("Use writeStringUtf8 instead", ReplaceWith("writeStringUtf8(s)"))
suspend fun ByteWriteChannel.writeUTF(s: String) {
    writeStringUtf8(s)
}

/**
 * See [java.io.DataOutput.writeChars]
 */
suspend fun ByteWriteChannel.writeChars(s: String) {
    for (ch in s) {
        writeShort(ch.toInt())
    }
}

/**
 * See [java.io.DataOutput.writeBytes]
 */
suspend fun ByteWriteChannel.writeBytes(s: String) {
    for (ch in s) {
        writeByte(ch.toInt())
    }
}

/**
 * See [java.io.DataOutput.write]
 */
@Deprecated("Use writeFully instead", ReplaceWith("writeFully(src)"))
suspend fun ByteWriteChannel.write(src: ByteArray) = writeFully(src)

/**
 * See [java.io.DataOutput.write]
 */
@Deprecated("Use writeFully instead", ReplaceWith("writeFully(src, offset, length)"))
suspend fun ByteWriteChannel.write(src: ByteArray, offset: Int, length: Int) = writeFully(src, offset, length)
