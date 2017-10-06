package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.internal.*
import kotlinx.io.core.*
import kotlinx.io.pool.*

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

fun WritePacket(headerSizeHint: Int = 0): ByteWritePacket = BytePacketBuilder(headerSizeHint)
