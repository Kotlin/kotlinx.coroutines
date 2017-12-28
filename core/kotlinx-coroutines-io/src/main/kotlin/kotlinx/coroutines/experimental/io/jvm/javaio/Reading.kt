package kotlinx.coroutines.experimental.io.jvm.javaio

import kotlinx.coroutines.experimental.io.*
import java.io.*

/**
 * Copies up to [limit] bytes from [this] input stream to CIO byte [channel] blocking on reading [this] stream
 * and suspending on [channel] if required
 *
 * @return number of bytes copied
 */
suspend fun InputStream.copyTo(channel: ByteWriteChannel, limit: Long = Long.MAX_VALUE): Long {
    require(limit >= 0) { "Limit shouldn't be negative: $limit" }
    val buffer = ByteArrayPool.borrow()

    try {
        var copied = 0L
        val bufferSize = buffer.size.toLong()
        while (copied < limit) {
            val rc = read(buffer, 0, minOf(limit - copied, bufferSize).toInt())
            if (rc == -1) break
            else if (rc > 0) {
                channel.writeFully(buffer, 0, rc)
                copied += rc
            }
        }

        return copied
    } finally {
        ByteArrayPool.recycle(buffer)
    }
}
