package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.internal.ObjectPool
import java.io.OutputStream
import java.nio.ByteBuffer
import java.nio.CharBuffer
import java.util.*

internal class ByteWritePacketImpl(private val pool: ObjectPool<ByteBuffer>) : ByteWritePacket {
    override var size: Int = 0
        private set
    private var buffers: Any? = null

    override fun writeFully(src: ByteArray, offset: Int, length: Int) {
        var copied = 0

        while (copied < length) {
            write(1) { buffer ->
                val size = minOf(buffer.remaining(), length - copied)
                buffer.put(src, offset + copied, size)
                copied += size
            }
        }

        size += length
    }

    override fun writeFully(src: ByteBuffer) {
        val s = src.remaining()
        while (src.hasRemaining()) {
            write(1) { buffer ->
                if (buffer.remaining() >= src.remaining()) {
                    buffer.put(src)
                } else {
                    while (buffer.hasRemaining() && src.hasRemaining()) {
                        buffer.put(src.get())
                    }
                }
            }
        }
        size += s
    }

    override fun writeLong(l: Long) {
        write(8) { it.putLong(l) }
        size += 8
    }

    override fun writeInt(i: Int) {
        write(4) { it.putInt(i) }
        size += 4
    }

    override fun writeShort(s: Short) {
        write(2) { it.putShort(s) }
        size += 2
    }

    override fun writeByte(b: Byte) {
        write(1) { it.put(b) }
        size += 1
    }

    override fun writeDouble(d: Double) {
        write(8) { it.putDouble(d) }
        size += 8
    }

    override fun writeFloat(f: Float) {
        write(4) { it.putFloat(f) }
        size += 4
    }

    override fun append(c: Char): ByteWritePacket {
        write(3) {
            size += it.putUtf8Char(c.toInt() and 0xffff)
        }
        return this
    }

    override fun append(csq: CharSequence, start: Int, end: Int): ByteWritePacket {
        appendASCII(csq, start, end)
        return this
    }

    private tailrec fun appendASCII(csq: CharSequence, start: Int, end: Int) {
        val bb = ensure()
        val limitedEnd = minOf(end, start + bb.remaining())

        for (i in start until limitedEnd) {
            val chi = csq[i].toInt() and 0xffff
            if (chi >= 0x80) {
                appendUTF8(csq, i, end, bb)
                return
            }

            bb.put(chi.toByte())
            size++
        }

        if (limitedEnd < end) {
            return appendASCII(csq, limitedEnd, end)
        }
    }

    // expects at least one byte remaining in [bb]
    private tailrec fun appendUTF8(csq: CharSequence, start: Int, end: Int, bb: ByteBuffer) {
        for (i in start .. end) {
            val chi = csq[i].toInt() and 0xffff
            val requiredSize = when {
                chi <= 0x7f -> 1
                chi > 0x7ff -> 3
                else -> 2
            }

            if (bb.remaining() < requiredSize) {
                return appendUTF8(csq, i, end, appendNewBuffer())
            }

            size += bb.putUtf8Char(chi)
        }
    }

    override fun writeStringUtf8(s: String) {
        append(s, 0, s.length)
    }

    override fun writeStringUtf8(cs: CharSequence) {
        append(cs, 0, cs.length)
    }

    override fun writeStringUtf8(cb: CharBuffer) {
        append(cb, 0, cb.remaining())
    }

    @Suppress("NOTHING_TO_INLINE")
    private inline fun ByteBuffer.putUtf8Char(v: Int) = when {
        v in 1..0x7f -> {
            put(v.toByte())
            1
        }
        v > 0x7ff -> {
            put((0xe0 or ((v shr 12) and 0x0f)).toByte())
            put((0x80 or ((v shr  6) and 0x3f)).toByte())
            put((0x80 or ( v         and 0x3f)).toByte())
            3
        }
        else -> {
            put((0xc0 or ((v shr  6) and 0x1f)).toByte())
            put((0x80 or ( v         and 0x3f)).toByte())
            2
        }
    }

    override fun outputStream(): OutputStream {
        return object : OutputStream() {
            override fun write(b: Int) {
                writeByte(b.toByte())
            }

            override fun write(b: ByteArray, off: Int, len: Int) {
                writeFully(b, off, len)
            }
        }
    }

    override fun build(): ByteReadPacket {
        val bs = buffers ?: return ByteReadPacketEmpty
        buffers = null

        return if (bs is ArrayDeque<*>) {
            @Suppress("UNCHECKED_CAST")
            when {
                bs.isEmpty() -> ByteReadPacketEmpty
                bs.size == 1 -> ByteReadPacketSingle((bs.first as ByteBuffer).also { it.flip() }, pool)
                else -> ByteReadPacketImpl((bs as ArrayDeque<ByteBuffer>).also {
                    for (b in bs) {
                        b.flip()
                    }
                }, pool)
            }
        } else {
            ByteReadPacketSingle((bs as ByteBuffer).also { it.flip() }, pool)
        }
    }

    override fun release() {
        val bs = buffers ?: return
        buffers = null
        size = 0

        if (bs is ArrayDeque<*>) {
            for (o in bs) {
                recycle(o as ByteBuffer)
            }
        } else {
            recycle(bs as ByteBuffer)
        }
    }

    private inline fun write(size: Int, block: (ByteBuffer) -> Unit) {
        val buffer = last()?.takeIf { it.remaining() >= size }

        if (buffer == null) {
            block(ensure())
        } else {
            block(buffer)
        }
    }

    private fun ensure(): ByteBuffer = last()?.takeIf { it.hasRemaining() } ?: appendNewBuffer()

    private fun appendNewBuffer(): ByteBuffer {
        val new = pool.borrow()
        new.clear()
        last(new)
        return new
    }

    private fun last(): ByteBuffer? = buffers?.let { b ->
        @Suppress("UNCHECKED_CAST")
        when (b) {
            is ByteBuffer -> b
            is ArrayDeque<*> -> (b as ArrayDeque<ByteBuffer>).takeIf { it.isNotEmpty() }?.peekLast()
            else -> null
        }
    }

    private fun last(new: ByteBuffer) {
        @Suppress("UNCHECKED_CAST")
        if (buffers is ArrayDeque<*>) (buffers as ArrayDeque<ByteBuffer>).addLast(new)
        else if (buffers == null) buffers = new
        else {
            val dq = ArrayDeque<ByteBuffer>()
            dq.addFirst(buffers as ByteBuffer)
            dq.addLast(new)
            buffers = dq
        }
    }

    private fun recycle(buffer: ByteBuffer) {
        pool.recycle(buffer)
    }
}