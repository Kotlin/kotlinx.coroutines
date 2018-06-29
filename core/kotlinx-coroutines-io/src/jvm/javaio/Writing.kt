/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io.jvm.javaio

import kotlinx.coroutines.experimental.io.*
import java.io.*

/**
 * Copies up to [limit] bytes from [this] byte channel to [out] stream suspending on read channel
 * and blocking on output
 *
 * @return number of bytes copied
 */
suspend fun ByteReadChannel.copyTo(out: OutputStream, limit: Long = Long.MAX_VALUE): Long {
    require(limit >= 0) { "Limit shouldn't be negative: $limit" }

    val buffer = ByteArrayPool.borrow()
    try {
        var copied = 0L
        val bufferSize = buffer.size.toLong()

        while (copied < limit) {
            val rc = readAvailable(buffer, 0, minOf(limit - copied, bufferSize).toInt())
            if (rc == -1) break
            if (rc > 0) {
                out.write(buffer, 0, rc)
                copied += rc
            }
        }

        return copied
    } finally {
        ByteArrayPool.recycle(buffer)
    }
}
