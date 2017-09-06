package kotlinx.coroutines.experimental.io.packet

import java.io.*
import java.nio.ByteBuffer
import kotlin.experimental.and

interface ByteReadPacket {
    val remaining: Int

    fun readAvailable(dst: ByteArray, offset: Int, length: Int): Int
    fun readAvailable(dst: ByteArray) = readAvailable(dst, 0, dst.size)
    fun readAvailable(dst: ByteBuffer): Int

    fun readFully(dst: ByteArray, offset: Int, length: Int)
    fun readFully(dst: ByteArray) = readFully(dst, 0, dst.size)
    fun readFully(dst: ByteBuffer): Int

    fun readLong(): Long
    fun readInt(): Int
    fun readShort(): Short
    fun readByte(): Byte

    fun readUInt(): Long = readInt().toLong() and 0xffffffff
    fun readUShort(): Int = readShort().toInt() and 0xffff
    fun readUByte(): Short = readByte().toShort() and 0xff

    fun readDouble(): Double
    fun readFloat(): Float

    fun skip(n: Int): Int
    fun skipExact(n: Int) {
        if (skip(n) != n) throw EOFException("Unable to skip $n bytes due to end of packet")
    }

    fun release()

    fun readUTF8LineTo(out: Appendable, limit: Int = Int.MAX_VALUE): Boolean

    fun inputStream(): InputStream
    fun readerUTF8(): Reader

    fun readText(): CharSequence
}