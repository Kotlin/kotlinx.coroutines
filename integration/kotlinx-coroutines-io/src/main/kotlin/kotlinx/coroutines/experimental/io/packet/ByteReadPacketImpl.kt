@file:Suppress("UsePropertyAccessSyntax")

package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.internal.*
import java.io.*
import java.nio.*
import java.nio.charset.*
import java.util.*

internal class ByteReadPacketImpl(private val packets: ArrayDeque<ByteBuffer>, private val pool: ObjectPool<ByteBuffer>) : ByteReadPacket {
    override val remaining: Int
        get() = packets.sumBy { it.remaining() }

    internal fun steal(): ByteBuffer = packets.pollFirst() ?: throw IllegalStateException("EOF")

    override fun readLazy(dst: ByteArray, offset: Int, length: Int): Int {
        var copied = 0

        val rc = reading(0) { buffer ->
            val size = minOf(buffer.remaining(), length - copied)
            buffer.get(dst, offset + copied, size)
            copied += size

            copied < length
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

            dst.hasRemaining()
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
        val rc = reading(8) { v = it.getLong(); false }
        if (!rc) throw EOFException("Couldn't read long from empty packet")
        return v
    }

    override fun readInt(): Int {
        var v = 0
        val rc = reading(4) { v = it.getInt(); false }
        if (!rc) throw EOFException("Couldn't read int from empty packet")
        return v
    }

    override fun readShort(): Short {
        var v: Short = 0
        val rc = reading(2) { v = it.getShort(); false }
        if (!rc) throw EOFException("Couldn't read short from empty packet")
        return v
    }

    override fun readByte(): Byte {
        var v: Byte = 0
        val rc = reading(1) { v = it.get(); false }
        if (!rc) throw EOFException("Couldn't read byte from empty packet")
        return v
    }

    override fun readDouble(): Double {
        var v = 0.0
        val rc = reading(8) { v = it.getDouble(); false }
        if (!rc) throw EOFException("Couldn't read double from empty packet")
        return v
    }

    override fun readFloat(): Float {
        var v = 0.0f
        val rc = reading(4) { v = it.getFloat(); false }
        if (!rc) throw EOFException("Couldn't read float from empty packet")
        return v
    }

    override fun readUTF8LineTo(out: Appendable, limit: Int): Boolean {
        var decoded = 0
        var size = 1
        var cr = false
        var end = false

        val rc = reading(size) { bb ->
            size = bb.decodeUTF8 { ch ->
                when (ch) {
                    '\r' -> {
                        if (cr) {
                            end = true
                            return@decodeUTF8 false
                        }
                        cr = true
                        true
                    }
                    '\n' -> {
                        return true
                    }
                    else -> {
                        if (cr) {
                            end = true
                            return@decodeUTF8 false
                        }

                        if (decoded == limit) throw BufferOverflowException()
                        decoded++
                        out.append(ch)
                        true
                    }
                }
            }

            !end && size == 0
        }

        if (!rc && size != 0) throw MalformedInputException(0)

        return rc
    }

    override fun skip(n: Int): Int {
        var skipped = 0

        reading(0) {
            val m = minOf(n - skipped, it.remaining())
            it.position(it.position() + m)
            skipped += m

            skipped < n
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
                val rc = reading(1) { v = it.get(); true }
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

    private inline fun reading(size: Int, block: (ByteBuffer) -> Boolean): Boolean {
        if (packets.isEmpty()) return false

        var visited = false
        var buffer = packets.peekFirst()
        var stop = false

        while (!stop) {
            if (buffer.hasRemaining()) {
                if (buffer.remaining() < size) {
                    if (!tryStealBytesFromNextBuffer(size, buffer)) return false
                }

                visited = true
                stop = !block(buffer)
            }

            if (!buffer.hasRemaining()) {
                packets.removeFirst()
                recycle(buffer)

                if (packets.isEmpty()) break
                buffer = packets.peekFirst()
            }
        }

        return visited
    }

    private fun tryStealBytesFromNextBuffer(size: Int, buffer: ByteBuffer): Boolean {
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
        return true
    }

    private fun recycle(buffer: ByteBuffer) {
        pool.recycle(buffer)
    }
}