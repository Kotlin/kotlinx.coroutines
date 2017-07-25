package kotlinx.coroutines.experimental.io.packet

import java.io.*
import java.nio.*
import kotlin.experimental.*

interface ByteReadPacket {
    val remaining: Int

    fun readLazy(dst: ByteArray, offset: Int, length: Int): Int
    fun readLazy(dst: ByteArray) = readLazy(dst, 0, dst.size)
    fun readLazy(dst: ByteBuffer): Int

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
    fun skipExact(n: Int)

    fun release()

    fun <A : Appendable> readUTF8LineTo(out: A, limit: Int = Int.MAX_VALUE): Boolean

    fun inputStream(): InputStream
}