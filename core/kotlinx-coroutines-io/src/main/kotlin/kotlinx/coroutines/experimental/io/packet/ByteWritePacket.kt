package kotlinx.coroutines.experimental.io.packet

import java.io.*
import java.nio.ByteBuffer
import java.nio.CharBuffer

interface ByteWritePacket : Appendable {
    val size: Int

    fun writeFully(src: ByteArray, offset: Int, length: Int)
    fun writeFully(src: ByteArray) = writeFully(src, 0, src.size)
    fun writeFully(src: ByteBuffer)

    fun writeLong(l: Long)
    fun writeInt(i: Int)
    fun writeShort(s: Short)
    fun writeByte(b: Byte)
    fun writeDouble(d: Double)
    fun writeFloat(f: Float)

    fun writeStringUtf8(s: String)
    fun writeStringUtf8(cb: CharBuffer)
    fun writeStringUtf8(cs: CharSequence)

    fun release()
    fun build(): ByteReadPacket

    fun outputStream(): OutputStream
    fun writerUTF8(): Writer

    fun writePacket(p: ByteReadPacket)
    fun writePacketUnconsumed(p: ByteReadPacket)

    override fun append(csq: CharSequence): ByteWritePacket {
        append(csq, 0, csq.length)
        return this
    }
}
