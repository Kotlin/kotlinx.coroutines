package kotlinx.coroutines.experimental.io.packet

import java.io.*
import java.nio.*

interface ByteWritePacket : Appendable {
    fun writeFully(src: ByteArray, offset: Int, length: Int)
    fun writeFully(src: ByteArray) = writeFully(src, 0, src.size)
    fun writeFully(src: ByteBuffer)

    fun writeLong(l: Long)
    fun writeInt(i: Int)
    fun writeShort(s: Short)
    fun writeByte(b: Byte)
    fun writeDouble(d: Double)
    fun writeFloat(f: Float)

    fun writeUtf8String(s: String)

    fun release()
    fun build(): ByteReadPacket

    fun outputStream(): OutputStream

    override fun append(csq: CharSequence): ByteWritePacket {
        append(csq, 0, csq.length)
        return this
    }
}
