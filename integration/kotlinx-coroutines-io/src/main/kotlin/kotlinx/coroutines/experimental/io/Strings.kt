package kotlinx.coroutines.experimental.io

suspend fun ByteBufferChannel.readASCIILine(estimate: Int = 16): String? {
    val sb = StringBuilder(estimate)
    return if (readUTF8LineTo(sb)) sb.toString() else null
}

suspend fun ByteBufferChannel.readUTF8Line(estimate: Int = 16): String? {
    val sb = StringBuilder(estimate)
    return if (readUTF8LineTo(sb)) sb.toString() else null
}
