package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.buffers.*
import kotlinx.coroutines.experimental.io.internal.*
import java.io.*
import java.nio.ByteBuffer
import java.nio.CharBuffer

internal class ByteWritePacketImpl(private var headerSizeHint: Int, private val pool: ObjectPool<BufferView>) : ByteWritePacket {
    init {
        require(headerSizeHint >= 0) { "shouldn't be negative: headerSizeHint = $headerSizeHint" }
    }

    override var size: Int = 0
        private set

    private var head: BufferView = BufferView.Empty
    private var tail: BufferView = head

    override fun writeFully(src: ByteArray, offset: Int, length: Int) {
        var copied = 0

        while (copied < length) {
            write(1) { buffer ->
                val size = minOf(buffer.writeRemaining, length - copied)
                buffer.write(src, offset + copied, size)
                copied += size
            }
        }

        size += length
    }

    override fun writeFully(src: ByteBuffer) {
        val s = src.remaining()
        while (src.hasRemaining()) {
            write(1) { buffer ->
                val srcSize = src.remaining()
                val capacity = buffer.writeRemaining

                if (capacity >= srcSize) {
                    buffer.write(src)
                } else {
                    val lim = src.limit()
                    src.limit(src.position() + capacity)
                    buffer.write(src)
                    src.limit(lim)
                }
            }
        }
        size += s
    }

    override fun writeLong(l: Long) {
        write(8) { it.writeLong(l) }
        size += 8
    }

    override fun writeInt(i: Int) {
        write(4) { it.writeInt(i) }
        size += 4
    }

    override fun writeShort(s: Short) {
        write(2) { it.writeShort(s) }
        size += 2
    }

    override fun writeByte(b: Byte) {
        write(1) { it.writeByte(b) }
        size += 1
    }

    override fun writeDouble(d: Double) {
        write(8) { it.writeDouble(d) }
        size += 8
    }

    override fun writeFloat(f: Float) {
        write(4) { it.writeFloat(f) }
        size += 4
    }

    override fun writeDirect(size: Int, block: (ByteBuffer) -> Unit) {
        write(size) {
            it.writeDirect(size, block)
        }
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

    override fun writePacket(p: ByteReadPacket) {
        when (p) {
            ByteReadPacketEmpty -> {}
            is ByteReadPacketViewBased -> writePacket2(p)
            else -> writeFully(p.readBytes())
        }
    }

    private fun writePacket2(p: ByteReadPacketViewBased) {
        val foreignStolen = p.steal()
        if (foreignStolen == null) {
            p.release()
            return
        }

        val tail = tail
        if (tail === BufferView.Empty) {
            head = foreignStolen
            this.tail = foreignStolen.tail()
            size = foreignStolen.remainingAll().toInt()
            return
        }

        val lastSize = tail.readRemaining
        val nextSize = foreignStolen.readRemaining

        val maxCopySize = PACKET_MAX_COPY_SIZE
        val appendSize = if (nextSize < maxCopySize && nextSize <= tail.endGap) {
            nextSize
        } else -1

        val prependSize = if (lastSize < maxCopySize && lastSize <= foreignStolen.startGap && foreignStolen.isExclusivelyOwned()) {
            lastSize
        } else -1

        if (appendSize == -1 && prependSize == -1) {
            // simply enqueue
            tail.next = foreignStolen
            this.tail = foreignStolen.tail()
            size = head.remainingAll().toInt()
        } else if (prependSize == -1 || appendSize <= prependSize) {
            // do append
            tail.writeBufferAppend(foreignStolen)
            tail.next = foreignStolen.next
            this.tail = foreignStolen.tail().takeUnless { it === foreignStolen } ?: tail
            foreignStolen.release(p.pool)
            size = head.remainingAll().toInt()
        } else if (appendSize == -1 || prependSize < appendSize) {
            // do prepend
            foreignStolen.writeBufferPrepend(tail)

            if (head === tail) {
                head = foreignStolen
            } else {
                var pre = head
                while (true) {
                    val next = pre.next!!
                    if (next === tail) break
                    pre = next
                }

                pre.next = foreignStolen
            }
            tail.release(pool)

            this.tail = foreignStolen.tail()
            size = head.remainingAll().toInt()
        } else {
            throw IllegalStateException("prep = $prependSize, app = $appendSize")
        }
    }

    private tailrec fun appendASCII(csq: CharSequence, start: Int, end: Int) {
        val bb = ensure()
        val limitedEnd = minOf(end, start + bb.writeRemaining)

        for (i in start until limitedEnd) {
            val chi = csq[i].toInt() and 0xffff
            if (chi >= 0x80) {
                appendUTF8(csq, i, end, bb)
                return
            }

            bb.writeByte(chi.toByte())
            size++
        }

        if (limitedEnd < end) {
            return appendASCII(csq, limitedEnd, end)
        }
    }

    // expects at least one byte remaining in [bb]
    private tailrec fun appendUTF8(csq: CharSequence, start: Int, end: Int, bb: BufferView) {
        var rem = bb.writeRemaining
        val limitedEnd = minOf(end, start + rem)

        for (i in start until limitedEnd) {
            val chi = csq[i].toInt() and 0xffff
            val requiredSize = when {
                chi <= 0x7f -> 1
                chi > 0x7ff -> 3
                else -> 2
            }

            if (rem < requiredSize) {
                return appendUTF8(csq, i, end, appendNewBuffer())
            }

            val chSize = bb.putUtf8Char(chi)
            rem -= chSize
            size += chSize
        }

        if (limitedEnd < end) {
            return appendUTF8(csq, limitedEnd, end, appendNewBuffer())
        }
    }

    private tailrec fun appendASCII(csq: CharArray, start: Int, end: Int) {
        val bb = ensure()
        val limitedEnd = minOf(end, start + bb.writeRemaining)

        for (i in start until limitedEnd) {
            val chi = csq[i].toInt() and 0xffff
            if (chi >= 0x80) {
                appendUTF8(csq, i, end, bb)
                return
            }

            bb.writeByte(chi.toByte())
            size++
        }

        if (limitedEnd < end) {
            return appendASCII(csq, limitedEnd, end)
        }
    }

    // expects at least one byte remaining in [bb]
    private tailrec fun appendUTF8(csq: CharArray, start: Int, end: Int, bb: BufferView) {
        val limitedEnd = minOf(end, start + bb.writeRemaining)
        for (i in start until limitedEnd) {
            val chi = csq[i].toInt() and 0xffff
            val requiredSize = when {
                chi <= 0x7f -> 1
                chi > 0x7ff -> 3
                else -> 2
            }

            if (bb.writeRemaining < requiredSize) {
                return appendUTF8(csq, i, end, appendNewBuffer())
            }

            size += bb.putUtf8Char(chi)
        }

        if (limitedEnd < end) {
            return appendUTF8(csq, limitedEnd, end, appendNewBuffer())
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
    private inline fun BufferView.putUtf8Char(v: Int) = when {
        v in 1..0x7f -> {
            writeByte(v.toByte())
            1
        }
        v > 0x7ff -> {
            writeByte((0xe0 or ((v shr 12) and 0x0f)).toByte())
            writeByte((0x80 or ((v shr  6) and 0x3f)).toByte())
            writeByte((0x80 or ( v         and 0x3f)).toByte())
            3
        }
        else -> {
            writeByte((0xc0 or ((v shr  6) and 0x1f)).toByte())
            writeByte((0x80 or ( v         and 0x3f)).toByte())
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

    override fun writerUTF8(): Writer {
        return object : Writer() {
            override fun write(cbuf: CharArray, off: Int, len: Int) {
                appendASCII(cbuf, off, len)
            }

            override fun flush() {
            }

            override fun close() {
            }
        }
    }

    override fun build(): ByteReadPacket {
        val head = this.head

        this.head = BufferView.Empty
        this.tail = BufferView.Empty
        this.size = 0

        if (head === BufferView.Empty) return ByteReadPacketViewBased.Empty
        return ByteReadPacketViewBased(head, pool)
    }

    override fun release() {
        val head = this.head
        val empty = BufferView.Empty

        if (head !== empty) {
            this.head = empty
            this.tail = empty
            head.releaseAll(pool)
            size = 0
        }
    }

    override fun reset() {
        release()
    }

    private inline fun write(size: Int, block: (BufferView) -> Unit) {
        val buffer = last()?.takeIf { it.writeRemaining >= size }

        if (buffer == null) {
            block(appendNewBuffer())
        } else {
            block(buffer)
        }
    }

    private fun ensure(): BufferView = last()?.takeIf { it.writeRemaining > 0 } ?: appendNewBuffer()

    private fun appendNewBuffer(): BufferView {
        val new = pool.borrow()
        if (head === BufferView.Empty) {
            new.reserveStartGap(headerSizeHint)
        }
        new.reserveEndGap(ByteReadPacketViewBased.ReservedSize)
        last(new)
        return new
    }

    private fun last(): BufferView? = tail.takeIf { it !== BufferView.Empty }

    private fun last(new: BufferView) {
        if (head === BufferView.Empty) {
            tail = new
            head = new
        } else {
            tail.next = new
            tail = new
        }
    }
}