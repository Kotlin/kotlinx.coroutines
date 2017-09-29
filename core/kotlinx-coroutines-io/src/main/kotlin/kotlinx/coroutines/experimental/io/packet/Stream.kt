package kotlinx.coroutines.experimental.io.packet

import java.io.*

fun OutputStream.writePacket(builder: ByteWritePacket.() -> Unit) {
    writePacket(buildPacket(block = builder))
}

fun OutputStream.writePacket(p: ByteReadPacket) {
    val s = p.remaining
    if (s == 0) return
    val buffer = ByteArray(s.coerceAtMost(4096))

    try {
        while (!p.isEmpty) {
            val size = p.readAvailable(buffer)
            write(buffer, 0, size)
        }
    } finally {
        p.release()
    }
}

fun InputStream.readPacketExact(n: Long): ByteReadPacket = readPacketImpl(n, n)
fun InputStream.readPacketAtLeast(n: Long): ByteReadPacket = readPacketImpl(n, Long.MAX_VALUE)
fun InputStream.readPacketAtMost(n: Long): ByteReadPacket = readPacketImpl(1L, n)

private fun InputStream.readPacketImpl(min: Long, max: Long): ByteReadPacket {
    require(min >= 0L)
    require(min <= max)

    val buffer = ByteArray(max.coerceAtMost(4096).toInt())
    val builder = WritePacket()

    var read = 0L

    try {
        while (read < min || (read == min && min == 0L)) {
            val remInt = minOf(max - read, Int.MAX_VALUE.toLong()).toInt()
            val rc = read(buffer, 0, minOf(remInt, buffer.size))
            if (rc == -1) throw EOFException("Premature end of stream: was read $read bytes of $min")
            read += rc
            builder.writeFully(buffer, 0, rc)
        }
    } catch (t: Throwable) {
        builder.release()
        throw t
    }

    return builder.build()
}