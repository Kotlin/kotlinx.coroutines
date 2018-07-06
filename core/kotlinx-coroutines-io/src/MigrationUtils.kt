/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io

/**
 * See [java.io.DataOutput.writeUTF]
 */
@Deprecated("Use writeStringUtf8 instead", ReplaceWith("writeStringUtf8(s)"))
suspend fun ByteWriteChannel.writeUTF(s: String) {
    return writeStringUtf8(s)
}

/**
 * See [java.io.DataOutput.writeChars]
 */
suspend fun ByteWriteChannel.writeChars(s: String) {
    val bb = ByteBuffer.allocate(s.length * 2)
    val cb = bb.asCharBuffer()

    for (ch in s) {
        cb.put(ch)
    }

    return writeFully(bb)
}

/**
 * See [java.io.DataOutput.writeBytes]
 */
suspend fun ByteWriteChannel.writeBytes(s: String) {
    val array = ByteArray(s.length)
    var rc = 0

    for (ch in s) {
        array[rc++] = ch.toByte()
    }

    return writeFully(array)
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
