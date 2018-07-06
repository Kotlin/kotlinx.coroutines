/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.io

suspend fun ByteReadChannel.readASCIILine(estimate: Int = 16, limit: Int = Int.MAX_VALUE): String? {
    val sb = StringBuilder(estimate)
    return if (readUTF8LineTo(sb, limit)) sb.toString() else null
}

suspend fun ByteReadChannel.readUTF8Line(estimate: Int = 16, limit: Int = Int.MAX_VALUE): String? {
    val sb = StringBuilder(estimate)
    return if (readUTF8LineTo(sb, limit)) sb.toString() else null
}

@Deprecated("Use readUTF8Line or readASCIILine instead", ReplaceWith("readUTF8Line(estimate, limit)"))
suspend fun ByteReadChannel.readLine(estimate: Int = 16, limit: Int = Int.MAX_VALUE): String? = readUTF8Line(estimate, limit)
