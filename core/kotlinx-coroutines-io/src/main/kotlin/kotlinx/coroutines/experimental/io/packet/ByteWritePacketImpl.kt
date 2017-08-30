package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.internal.ObjectPool
import java.io.OutputStream
import java.nio.ByteBuffer
import java.nio.CharBuffer
import java.util.*

internal class ByteWritePacketImpl(private val pool: ObjectPool<ByteBuffer>) : ByteWritePacket {
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
    }

    override fun writeFully(src: ByteBuffer) {
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
    }

    override fun writeLong(l: Long) {
        write(8) { it.putLong(l) }
    }

    override fun writeInt(i: Int) {
        write(4) { it.putInt(i) }
    }

    override fun writeShort(s: Short) {
        write(2) { it.putShort(s) }
    }

    override fun writeByte(b: Byte) {
        write(1) { it.put(b) }
    }

    override fun writeDouble(d: Double) {
        write(8) { it.putDouble(d) }
    }

    override fun writeFloat(f: Float) {
        write(4) { it.putFloat(f) }
    }

    override fun append(c: Char): ByteWritePacket {
        write(3) {
            it.putUtf8Char(c.toInt() and 0xffff)
        }
        return this
    }

    override fun append(csq: CharSequence, start: Int, end: Int): ByteWritePacket {
        val length = end - start
        var w = 0
        var requiredSize = 1

        while (w < length) {
            write(requiredSize) { bb ->
                while (w < length) {
                    val ch = csq[start + w]
                    val v = ch.toInt() and 0xffff

                    requiredSize = when {
                        v in 1..0x7f -> 1
                        v > 0x7ff -> 3
                        else -> 2
                    }

                    if (bb.remaining() >= requiredSize) {
                        bb.putUtf8Char(v)
                        w++
                    } else {
                        break
                    }
                }
            }
        }

        return this
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
    private inline fun ByteBuffer.putUtf8Char(v: Int) {
        when {
            v in 1..0x7f -> put(v.toByte())
            v > 0x7ff -> {
                put((0xe0 or ((v shr 12) and 0x0f)).toByte())
                put((0x80 or ((v shr  6) and 0x3f)).toByte())
                put((0x80 or ( v         and 0x3f)).toByte())
            }
            else -> {
                put((0xc0 or ((v shr  6) and 0x1f)).toByte())
                put((0x80 or ( v         and 0x3f)).toByte())
            }
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
            val new = pool.borrow()
            last(new)
            new.clear()
            block(new)
        } else {
            block(buffer)
        }
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