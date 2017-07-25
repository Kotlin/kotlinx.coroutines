package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.internal.*
import java.nio.*

private val DirectBufferPool: ObjectPool<ByteBuffer> = ObjectPoolImpl(128, {
    ByteBuffer.allocateDirect(4096)
})

fun buildPacket(block: ByteWritePacket.() -> Unit): ByteReadPacket =
        ByteWritePacketImpl(DirectBufferPool).apply(block).build()

fun ByteReadPacket.readUTF8Line(estimate: Int = 16, limit: Int = Int.MAX_VALUE): String? {
    val sb = StringBuilder(estimate)
    return if (readUTF8LineTo(sb, limit)) sb.toString() else null
}
