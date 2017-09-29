package kotlinx.coroutines.experimental.io.packet

import kotlinx.coroutines.experimental.io.ByteBuffer
import kotlinx.coroutines.experimental.io.buffers.*
import kotlinx.coroutines.experimental.io.internal.*
import java.io.*
import java.nio.charset.*

internal class ByteReadPacketViewBased(private var head: BufferView,
                                       internal val pool: ObjectPool<BufferView>) : ByteReadPacket {

    override val remaining: Int
        get() = head.remainingAll().toInt() // TODO Long or Int?

    override val isEmpty: Boolean
        get() = head.isEmpty()

    override fun copy(): ByteReadPacket = ByteReadPacketViewBased(head.copyAll(), pool)

    override fun release() {
        if (head !== BufferView.Empty) {
            head.releaseAll(pool)
            head = BufferView.Empty
        }
    }

    fun steal(): BufferView? {
        val head = head
        val next = head.next
        val empty = BufferView.Empty
        if (head === empty) return null

        this.head = next ?: empty

        return head
    }

    override fun readByte() = readN(1) { readByte() }
    override fun readShort() = readN(2) { readShort() }
    override fun readInt() = readN(4) { readInt() }
    override fun readLong() = readN(8) { readLong() }
    override fun readFloat() = readN(4) { readFloat() }
    override fun readDouble() = readN(8) { readDouble() }

    override fun readAvailable(dst: ByteBuffer) = readAsMuchAsPossible(dst, 0)
    override fun readFully(dst: ByteBuffer): Int {
        val rc = readAsMuchAsPossible(dst, 0)
        if (dst.hasRemaining()) throw EOFException("Not enough data in packet to fill buffer: ${dst.remaining()} more bytes required")
        return rc
    }

    override fun readAvailable(dst: ByteArray, offset: Int, length: Int): Int {
        require(offset >= 0) { "offset shouldn't be negative: $offset" }
        require(length >= 0) { "length shouldn't be negative: $length" }
        require(offset + length <= dst.size) { throw ArrayIndexOutOfBoundsException() }

        return readAsMuchAsPossible(dst, offset, length, 0)
    }

    override fun readFully(dst: ByteArray, offset: Int, length: Int) {
        val rc = readAvailable(dst, offset, length)
        if (rc != length) throw EOFException("Not enough data in packet to fill buffer: ${length - rc} more bytes required")
    }

    override fun skip(n: Int) = discardAsMuchAsPossible(n, 0)

    override fun readUTF8LineTo(out: Appendable, limit: Int): Boolean {
        var decoded = 0
        var size = 1
        var cr = false
        var end = false

        while (!end) {
            val buffer = prepareRead(size)
            if (buffer == null) {
                if (size == 1) break
                throw MalformedInputException(0)
            }
            size = buffer.decodeUTF8 { ch ->
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
                        afterRead()
                        return true
                    }
                    else -> {
                        if (cr) {
                            end = true
                            return@decodeUTF8 false
                        }

                        if (decoded == limit) {
                            afterRead()
                            throw BufferLimitExceededException("Too many characters in line: limit $limit exceeded")
                        }
                        decoded++
                        out.append(ch)
                        true
                    }
                }
            }

            if (size == 0 || end) {
                afterRead()
                size = 1
            }
        }

        return decoded > 0 || !isEmpty
    }

    override fun readText(): CharSequence {
        return buildString(remaining) {
            while (true) {
                val bb = prepareRead(1) ?: break
                if (!bb.decodeASCII { append(it); true }) {
                    readTextUtf8()
                    break
                }
                afterRead()
            }
        }
    }

    private fun StringBuilder.readTextUtf8() {
        var size = 1
        while (true) {
            val bb = prepareRead(size)
            if (bb == null) {
                if (size == 1) break
                throw MalformedInputException(0)
            }

            size = bb.decodeUTF8 { append(it); true }
            if (size == 0) {
                afterRead()
                size = 1
            }
        }
    }

    override fun readerUTF8(): Reader {
        return object : Reader() {
            override fun close() {
                release()
            }

            override fun skip(n: Long): Long {
                var skipped = 0L
                val buffer = SkipBuffer
                val bufferSize = buffer.size

                while (skipped < n) {
                    val size = minOf(bufferSize.toLong(), n - skipped).toInt()
                    val rc = read(buffer, 0, size)
                    if (rc == -1) break
                    skipped += rc
                }

                return skipped
            }

            override fun read(cbuf: CharArray, off: Int, len: Int): Int {
                var rem = len
                var idx = off

                while (rem > 0) {
                    val bb = prepareRead(1) ?: break
                    val rc = bb.decodeASCII {
                        if (rem == 0) false
                        else {
                            cbuf[idx++] = it
                            rem--
                            true
                        }
                    }

                    if (rc) {
                        afterRead()
                    } else if (rem == 0) {
                        break
                    } else {
                        return readUtf8(cbuf, idx, rem, idx - off)
                    }
                }

                val copied = idx - off
                return when {
                    copied > 0 -> copied
                    head.isEmpty() -> -1
                    else -> 0
                }
            }

            private fun readUtf8(cbuf: CharArray, off: Int, len: Int, copied0: Int): Int {
                var size = 1
                var rem = len
                var idx = off

                while (rem > 0) {
                    val buffer = prepareRead(size)
                    if (buffer == null) {
                        if (size == 1) break
                        throw MalformedInputException(0)
                    }

                    size = buffer.decodeUTF8 {
                        if (rem == 0) false
                        else {
                            cbuf[idx++] = it
                            rem--
                            true
                        }
                    }

                    if (size == 0) {
                        afterRead()
                        size = 1
                    }
                }

                val copied = idx - off + copied0
                return when {
                    copied > 0 -> copied
                    head.isEmpty() -> -1
                    else -> 0
                }
            }
        }
    }

    override fun inputStream(): InputStream {
        return object : InputStream() {
            override fun read(): Int {
                if (head.isEmpty()) return -1
                return readByte().toInt() and 0xff
            }

            override fun available() = remaining

            override fun close() {
                release()
            }
        }
    }

    private tailrec fun discardAsMuchAsPossible(n: Int, skipped: Int): Int {
        if (n == 0) return skipped
        val current = prepareRead(1) ?: return skipped
        val size = minOf(current.readRemaining, n)
        if (current.discardExact(size)) {
            afterRead()
        }

        return discardAsMuchAsPossible(n - size, skipped + size)
    }

    private tailrec fun readAsMuchAsPossible(bb: ByteBuffer, copied: Int): Int {
        if (!bb.hasRemaining()) return copied
        val current = prepareRead(1) ?: return copied
        val destinationCapacity = bb.remaining()
        val available = current.readRemaining

        return if (destinationCapacity >= available) {
            current.read(bb, available)
            releaseHead(current)

            readAsMuchAsPossible(bb, copied + available)
        } else {
            current.read(bb, destinationCapacity)

            copied + destinationCapacity
        }
    }

    private tailrec fun readAsMuchAsPossible(array: ByteArray, offset: Int, length: Int, copied: Int): Int {
        if (length == 0) return copied
        val current = prepareRead(1) ?: return copied
        val size = minOf(length, current.readRemaining)

        current.read(array, offset, size)
        return if (size != length || current.readRemaining == 0) {
            afterRead()
            readAsMuchAsPossible(array, offset + size, length - size, copied + size)
        } else {
            copied + size
        }
    }

    private inline fun <R> readN(n: Int, block: BufferView.() -> R): R {
        val bb = prepareRead(n) ?: throw EOFException("Not enough data in packet to read $n byte(s)")
        val rc = block(bb)
        afterRead()
        return rc
    }

    private tailrec fun prepareRead(minSize: Int): BufferView? {
        val head = head

        val headSize = head.readRemaining
        if (headSize >= minSize) return head
        val next = head.next ?: return null

        head.writeBufferAppend(next, minSize)
        if (next.readRemaining == 0) {
            head.next = next.next
            next.release(pool)
        }

        if (head.readRemaining >= minSize) return head
        if (minSize > ReservedSize) throw IllegalStateException("minSize of $minSize is too big (should be less than $ReservedSize")

        return prepareRead(minSize)
    }

    private fun afterRead() {
        val head = head
        if (head.readRemaining == 0) {
            releaseHead(head)
        }
    }

    private fun releaseHead(head: BufferView) {
        val next = head.next
        this.head = next ?: BufferView.Empty
        head.release(pool)
    }

    companion object {
        val Empty = ByteReadPacketViewBased(BufferView.Empty, object: NoPoolImpl<BufferView>() {
            override fun borrow() = BufferView.Empty
        })
        val ReservedSize = 8
        private val SkipBuffer = CharArray(8192)
    }
}

