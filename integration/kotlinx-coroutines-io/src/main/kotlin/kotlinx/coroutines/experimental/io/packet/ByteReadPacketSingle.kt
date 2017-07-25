package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.internal.*
import java.io.*
import java.nio.*

internal class ByteReadPacketSingle(private var buffer: ByteBuffer?, private val pool: ObjectPool<ByteBuffer>) : ByteReadPacket {
    override val remaining: Int
        get() = buffer?.remaining() ?: 0

    override fun readLazy(dst: ByteArray, offset: Int, length: Int): Int {
        var copied = 0

        val rc = reading { buffer ->
            val size = minOf(buffer.remaining(), length - copied)
            buffer.get(dst, offset, size)
            copied += size

            if (copied == length) return copied
        }

        return if (rc) copied else -1
    }

    override fun readLazy(dst: ByteBuffer): Int {
        var copied = 0

        val rc = reading { buffer ->
            if (dst.remaining() >= buffer.remaining()) {
                copied += buffer.remaining()
                dst.put(buffer)
            } else {
                while (dst.hasRemaining() && buffer.hasRemaining()) {
                    dst.put(buffer.get())
                    copied++
                }
            }

            if (!dst.hasRemaining()) return copied
        }

        return if (rc) copied else -1
    }

    override fun readFully(dst: ByteArray, offset: Int, length: Int) {
        val rc = readLazy(dst, offset, length)
        if (rc < length) throw EOFException("Not enough bytes in the packet")
    }

    override fun readFully(dst: ByteBuffer): Int {
        val rc = readLazy(dst)
        if (dst.hasRemaining()) throw EOFException("Not enough bytes in the packet")
        return rc
    }

    override fun readLong(): Long {
        var v = 0L
        val rc = reading { v = it.getLong() }
        if (!rc) throw EOFException("Couldn't read long from empty packet")
        return v
    }

    override fun readInt(): Int {
        var v = 0
        val rc = reading { v = it.getInt() }
        if (!rc) throw EOFException("Couldn't read int from empty packet")
        return v
    }

    override fun readShort(): Short {
        var v: Short = 0
        val rc = reading { v = it.getShort() }
        if (!rc) throw EOFException("Couldn't read short from empty packet")
        return v
    }

    override fun readByte(): Byte {
        var v: Byte = 0
        val rc = reading { v = it.get() }
        if (!rc) throw EOFException("Couldn't read byte from empty packet")
        return v
    }

    override fun readDouble(): Double {
        var v = 0.0
        val rc = reading { v = it.getDouble() }
        if (!rc) throw EOFException("Couldn't read double from empty packet")
        return v
    }

    override fun readFloat(): Float {
        var v = 0.0f
        val rc = reading { v = it.getFloat() }
        if (!rc) throw EOFException("Couldn't read float from empty packet")
        return v
    }

    override fun <A : Appendable> readUTF8LineTo(out: A, limit: Int): Boolean {
        TODO()
    }

    override fun skip(n: Int): Int {
        var skipped = 0

        reading {
            val m = minOf(n - skipped, it.remaining())
            it.position(it.position() + m)
            skipped += m
        }

        return skipped
    }

    override fun skipExact(n: Int) {
        if (skip(n) != n) throw EOFException("Unable to skip $n bytes due to end of packet")
    }

    override fun inputStream(): InputStream {
        return object : InputStream() {
            override fun read(): Int {
                var v: Byte = 0
                val rc = reading { v = it.get() }
                return if (rc) v.toInt() and 0xff else -1
            }

            override fun read(b: ByteArray, off: Int, len: Int) = readLazy(b, off, len)
            override fun skip(n: Long): Long {
                if (n > Int.MAX_VALUE) return this@ByteReadPacketSingle.skip(Int.MAX_VALUE).toLong()
                return this@ByteReadPacketSingle.skip(n.toInt()).toLong()
            }

            override fun available() = remaining
        }
    }

    override fun release() {
        recycle(buffer ?: return)
        buffer = null
    }

    private inline fun reading(block: (ByteBuffer) -> Unit): Boolean {
        val buffer = buffer ?: return false

        if (!buffer.hasRemaining()) {
            this.buffer = null
            recycle(buffer)
            return false
        }

        block(buffer)

        if (!buffer.hasRemaining()) {
            this.buffer = null
            recycle(buffer)
        }

        return true
    }

    private fun recycle(buffer: ByteBuffer) {
        pool.recycle(buffer)
    }
}