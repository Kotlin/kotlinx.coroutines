package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.buffers.*
import kotlinx.coroutines.experimental.io.internal.*

internal val PACKET_BUFFER_SIZE = getIOIntProperty("PacketBufferSize", 4096)
internal val PACKET_BUFFER_POOL_SIZE = getIOIntProperty("PacketBufferPoolSize", 128)
internal val PACKET_MAX_COPY_SIZE = getIOIntProperty("PacketMaxCopySize", 500)

internal inline fun buildPacket(pool: ObjectPool<BufferView> = BufferView.Pool, headerSizeHint: Int, block: ByteWritePacket.() -> Unit): ByteReadPacket {
    val w = ByteWritePacketImpl(headerSizeHint, pool)
    try {
        block(w)
        return w.build()
    } catch (t: Throwable) {
        w.release()
        throw t
    }
}

inline fun buildPacket(headerSizeHint: Int = 0, block: ByteWritePacket.() -> Unit): ByteReadPacket {
    val w = WritePacket(headerSizeHint)
    try {
        block(w)
        return w.build()
    } catch (t: Throwable) {
        w.release()
        throw t
    }
}

fun WritePacket(headerSizeHint: Int = 0): ByteWritePacket = ByteWritePacketImpl(headerSizeHint, BufferView.Pool)

fun ByteReadPacket.readUTF8Line(estimate: Int = 16, limit: Int = Int.MAX_VALUE): String? {
    val sb = StringBuilder(estimate)
    return if (readUTF8LineTo(sb, limit)) sb.toString() else null
}

fun ByteReadPacket.readBytes(n: Int = remaining): ByteArray = ByteArray(n).also { readFully(it) }
