package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.internal.*
import java.nio.ByteBuffer

internal val PACKET_BUFFER_SIZE = getIOIntProperty("PacketBufferSize", 4096)
private val PACKET_BUFFER_POOL_SIZE = getIOIntProperty("PacketBufferPoolSize", 128)
internal val PACKET_MAX_COPY_SIZE = getIOIntProperty("PacketMaxCopySize", 500)

internal val PacketBufferPool: ObjectPool<ByteBuffer> =
    object : ObjectPoolImpl<ByteBuffer>(PACKET_BUFFER_POOL_SIZE) {
        override fun produceInstance(): ByteBuffer = ByteBuffer.allocateDirect(PACKET_BUFFER_SIZE)
        override fun clearInstance(instance: ByteBuffer) = instance.apply { clear() }
    }

internal inline fun buildPacket(pool: ObjectPool<ByteBuffer> = PacketBufferPool, headerSizeHint: Int, block: ByteWritePacket.() -> Unit): ByteReadPacket {
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

fun WritePacket(headerSizeHint: Int = 0): ByteWritePacket = ByteWritePacketImpl(headerSizeHint, PacketBufferPool)

fun ByteReadPacket.readUTF8Line(estimate: Int = 16, limit: Int = Int.MAX_VALUE): String? {
    val sb = StringBuilder(estimate)
    return if (readUTF8LineTo(sb, limit)) sb.toString() else null
}

fun ByteReadPacket.readBytes(n: Int = remaining): ByteArray = ByteArray(n).also { readFully(it) }
