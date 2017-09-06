package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.internal.*
import java.nio.ByteBuffer

internal val PACKET_BUFFER_SIZE = getIOIntProperty("PacketBufferSize", 4096)
private val PACKET_BUFFER_POOL_SIZE = getIOIntProperty("PacketBufferPoolSize", 128)

private val PacketBufferPool: ObjectPool<ByteBuffer> =
    object : ObjectPoolImpl<ByteBuffer>(PACKET_BUFFER_POOL_SIZE) {
        override fun produceInstance(): ByteBuffer = ByteBuffer.allocateDirect(PACKET_BUFFER_SIZE)
    }

inline fun buildPacket(block: ByteWritePacket.() -> Unit): ByteReadPacket =
        WritePacket().apply(block).build()

fun WritePacket(): ByteWritePacket = ByteWritePacketImpl(PacketBufferPool)

fun ByteReadPacket.readUTF8Line(estimate: Int = 16, limit: Int = Int.MAX_VALUE): String? {
    val sb = StringBuilder(estimate)
    return if (readUTF8LineTo(sb, limit)) sb.toString() else null
}

fun ByteReadPacket.readBytes() = inputStream().readBytes(remaining)
