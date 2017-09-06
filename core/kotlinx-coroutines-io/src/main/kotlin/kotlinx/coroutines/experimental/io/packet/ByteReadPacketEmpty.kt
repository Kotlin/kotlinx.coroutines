package kotlinx.coroutines.experimental.io.packet

import java.io.*
import java.nio.*

object ByteReadPacketEmpty : ByteReadPacket {
    override val remaining: Int
        get() = 0

    override fun readAvailable(dst: ByteArray, offset: Int, length: Int) = -1
    override fun readAvailable(dst: ByteBuffer): Int = -1

    override fun readFully(dst: ByteArray, offset: Int, length: Int) {
        if (length > 0) throw EOFException("Couldn't read $length bytes from empty packet")
    }

    override fun readFully(dst: ByteBuffer): Int {
        if (dst.hasRemaining()) throw EOFException("Couldn't read ${dst.remaining()} bytes from empty packet")
        return 0
    }

    override fun readLong(): Long {
        throw EOFException("Couldn't read long from empty packet")
    }

    override fun readInt(): Int {
        throw EOFException("Couldn't read int from empty packet")
    }

    override fun readShort(): Short {
        throw EOFException("Couldn't read short from empty packet")
    }

    override fun readByte(): Byte {
        throw EOFException("Couldn't read byte from empty packet")
    }

    override fun readDouble(): Double {
        throw EOFException("Couldn't read double from empty packet")
    }

    override fun readFloat(): Float {
        throw EOFException("Couldn't read float from empty packet")
    }

    override fun skip(n: Int) = 0

    override fun release() {
    }

    override fun readUTF8LineTo(out: Appendable, limit: Int) = false

    override fun inputStream(): InputStream = EmptyInputStream
    override fun readerUTF8(): Reader = EmptyReader

    private object EmptyInputStream : InputStream() {
        override fun available() = 0

        override fun read(): Int = -1
        override fun read(b: ByteArray?, off: Int, len: Int): Int = -1
        override fun read(b: ByteArray?) = -1

        override fun skip(n: Long) = 0L

        override fun markSupported() = true
        override fun mark(readlimit: Int) {
        }

        override fun reset() {
        }

        override fun close() {
        }
    }

    private object EmptyReader : Reader() {
        override fun close() {
        }

        override fun read(cbuf: CharArray?, off: Int, len: Int) = -1
        override fun read() = -1
        override fun read(target: CharBuffer?) = -1
    }
}