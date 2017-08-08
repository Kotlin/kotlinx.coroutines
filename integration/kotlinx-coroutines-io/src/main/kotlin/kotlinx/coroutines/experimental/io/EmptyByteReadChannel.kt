package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.io.packet.*
import java.nio.*

object EmptyByteReadChannel : ByteReadChannel {
    override val remaining: Int get() = 0
    override val isClosedForReceive: Boolean get() = true
    override var readByteOrder: ByteOrder
        get() = ByteOrder.BIG_ENDIAN
        set(value) {}

    suspend override fun readLazy(dst: ByteArray, offset: Int, length: Int): Int = -1

    suspend override fun readLazy(dst: ByteBuffer): Int {
        return -1
    }

    suspend override fun readPacket(size: Int): ByteReadPacket {
        if (size != 0) throw ClosedReceiveChannelException("EOF")
        return ByteReadPacketEmpty
    }

    suspend override fun readFully(dst: ByteArray, offset: Int, length: Int) {
        if (length != 0) throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun readFully(dst: ByteBuffer): Int {
        if (dst.hasRemaining()) throw ClosedReceiveChannelException("EOF")
        return 0
    }

    suspend override fun readLong(): Long {
        throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun readInt(): Int {
        throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun readShort(): Short {
        throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun readByte(): Byte {
        throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun readBoolean(): Boolean {
        throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun readUInt(): Long {
        throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun readUShort(): Int {
        throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun readUByte(): Short {
        throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun readDouble(): Double {
        throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun readFloat(): Float {
        throw ClosedReceiveChannelException("EOF")
    }

    suspend override fun lookAhead(visitor: (buffer: ByteBuffer, last: Boolean) -> Boolean) {
        visitor(ByteBuffer.allocate(0), true)
    }

    suspend override fun <A : Appendable> readUTF8LineTo(out: A, limit: Int): Boolean {
        return false
    }
}