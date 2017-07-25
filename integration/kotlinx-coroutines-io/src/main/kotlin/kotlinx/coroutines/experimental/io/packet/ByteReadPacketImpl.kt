@file:Suppress("UsePropertyAccessSyntax")

package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.internal.*
import java.io.*
import java.nio.*
import java.util.*

internal class ByteReadPacketImpl(private val packets: ArrayDeque<ByteBuffer>, private val pool: ObjectPool<ByteBuffer>) : ByteReadPacket {
    override val remaining: Int
        get() = packets.sumBy { it.remaining() }

    override fun readLazy(dst: ByteArray, offset: Int, length: Int): Int {
        var copied = 0

        val rc = reading(0) { buffer ->
            val size = minOf(buffer.remaining(), length - copied)
            buffer.get(dst, offset + copied, size)
            copied += size

            if (copied == length) return copied
        }

        return if (rc) copied else -1
    }

    override fun readLazy(dst: ByteBuffer): Int {
        var copied = 0

        val rc = reading(0) { buffer ->
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
        val rc = reading(8) { v = it.getLong() }
        if (!rc) throw EOFException("Couldn't read long from empty packet")
        return v
    }

    override fun readInt(): Int {
        var v = 0
        val rc = reading(4) { v = it.getInt() }
        if (!rc) throw EOFException("Couldn't read int from empty packet")
        return v
    }

    override fun readShort(): Short {
        var v: Short = 0
        val rc = reading(2) { v = it.getShort() }
        if (!rc) throw EOFException("Couldn't read short from empty packet")
        return v
    }

    override fun readByte(): Byte {
        var v: Byte = 0
        val rc = reading(1) { v = it.get() }
        if (!rc) throw EOFException("Couldn't read byte from empty packet")
        return v
    }

    override fun readDouble(): Double {
        var v = 0.0
        val rc = reading(8) { v = it.getDouble() }
        if (!rc) throw EOFException("Couldn't read double from empty packet")
        return v
    }

    override fun readFloat(): Float {
        var v = 0.0f
        val rc = reading(4) { v = it.getFloat() }
        if (!rc) throw EOFException("Couldn't read float from empty packet")
        return v
    }

    override fun <A : Appendable> readUTF8LineTo(out: A, limit: Int): Boolean {
        TODO()
    }

    override fun skip(n: Int): Int {
        var skipped = 0

        reading(0) {
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
                val rc = reading(1) { v = it.get() }
                return if (rc) v.toInt() and 0xff else -1
            }

            override fun read(b: ByteArray, off: Int, len: Int) = readLazy(b, off, len)
            override fun skip(n: Long): Long {
                if (n > Int.MAX_VALUE) return this@ByteReadPacketImpl.skip(Int.MAX_VALUE).toLong()
                return this@ByteReadPacketImpl.skip(n.toInt()).toLong()
            }

            override fun available() = remaining
        }
    }

    override fun release() {
        while (packets.isNotEmpty()) {
            recycle(packets.remove())
        }
    }

    private inline fun reading(size: Int, block: (ByteBuffer) -> Unit): Boolean {
        var visited = false

        while (packets.isNotEmpty()) {
            val buffer = packets.peekFirst()

            if (buffer.hasRemaining()) {
                if (buffer.remaining() < size) {
                    if (packets.size == 1) {
                        return false
                    }

                    packets.removeFirst()

                    val extraBytes = size - buffer.remaining()
                    val next = packets.peekFirst()

                    buffer.compact()
                    repeat(extraBytes) {
                        buffer.put(next.get())
                    }
                    buffer.flip()

                    packets.addFirst(buffer)
                }

                visited = true
                block(buffer)
            }

            if (!buffer.hasRemaining()) {
                packets.removeFirst()
                recycle(buffer)
            }
        }

        return visited
    }

    private fun recycle(buffer: ByteBuffer) {
        pool.recycle(buffer)
    }
}