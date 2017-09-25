package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.buffers.*
import kotlinx.coroutines.experimental.io.packet.*
import org.junit.*
import java.io.*
import java.nio.ByteBuffer
import kotlin.test.*

class BytePacketBuildTest {
    @get:Rule
    private val pool = VerifyingObjectPool(BufferView.Pool)

    @Test
    fun smokeSingleBufferTest() {
        val p = buildPacket {
            writeFully(ByteArray(2))
            writeFully(ByteBuffer.allocate(3))

            writeByte(0x12)
            writeShort(0x1234)
            writeInt(0x12345678)
            writeDouble(1.23)
            writeFloat(1.23f)
            writeLong(0x123456789abcdef0)

            writeStringUtf8("OK\n")
            listOf(1, 2, 3).joinTo(this, separator = "|")
        }

        assertEquals(2 + 3 + 1 + 2 + 4 + 8 + 4 + 8 + 3 + 5, p.remaining)

        p.readFully(ByteArray(2))
        p.readFully(ByteBuffer.allocate(3))

        assertEquals(0x12, p.readByte())
        assertEquals(0x1234, p.readShort())
        assertEquals(0x12345678, p.readInt())
        assertEquals(1.23, p.readDouble())
        assertEquals(1.23f, p.readFloat())
        assertEquals(0x123456789abcdef0, p.readLong())

        assertEquals("OK", p.readUTF8Line())
        assertEquals("1|2|3", p.readUTF8Line())
    }

    @Test
    fun smokeMultiBufferTest() {
        val p = buildPacket {
            writeFully(ByteArray(9999))
            writeFully(ByteBuffer.allocate(8888))
            writeByte(0x12)
            writeShort(0x1234)
            writeInt(0x12345678)
            writeDouble(1.23)
            writeFloat(1.23f)
            writeLong(0x123456789abcdef0)

            writeStringUtf8("OK\n")
            listOf(1, 2, 3).joinTo(this, separator = "|")
        }

        assertEquals(9999 + 8888 + 1 + 2 + 4 + 8 + 4 + 8 + 3 + 5, p.remaining)

        p.readFully(ByteArray(9999))
        p.readFully(ByteBuffer.allocate(8888))
        assertEquals(0x12, p.readByte())
        assertEquals(0x1234, p.readShort())
        assertEquals(0x12345678, p.readInt())
        assertEquals(1.23, p.readDouble())
        assertEquals(1.23f, p.readFloat())
        assertEquals(0x123456789abcdef0, p.readLong())

        assertEquals("OK", p.readUTF8Line())
        assertEquals("1|2|3", p.readUTF8Line())
    }

    @Test
    fun testSingleBufferSkipTooMuch() {
        val p = buildPacket {
            writeFully(ByteArray(9999))
        }

        assertEquals(9999, p.skip(10000))
    }

    @Test
    fun testSingleBufferSkip() {
        val p = buildPacket {
            writeFully("ABC123".toByteArray())
        }

        assertEquals(3, p.skip(3))
        assertEquals("123", p.readUTF8Line())
    }

    @Test
    fun testSingleBufferSkipExact() {
        val p = buildPacket {
            writeFully("ABC123".toByteArray())
        }

        p.skipExact(3)
        assertEquals("123", p.readUTF8Line())
    }

    @Test(expected = EOFException::class)
    fun testSingleBufferSkipExactTooMuch() {
        val p = buildPacket {
            writeFully("ABC123".toByteArray())
        }

        p.skipExact(1000)
    }

    @Test
    fun testMultiBufferSkipTooMuch() {
        val p = buildPacket {
            writeFully(ByteArray(99999))
        }

        assertEquals(99999, p.skip(1000000))
    }

    @Test
    fun testMultiBufferSkip() {
        val p = buildPacket {
            writeFully(ByteArray(99999))
            writeFully("ABC123".toByteArray())
        }

        assertEquals(99999 + 3, p.skip(99999 + 3))
        assertEquals("123", p.readUTF8Line())
    }

    @Test
    fun testNextBufferBytesStealing() {
        val p = buildPacket {
            repeat(PACKET_BUFFER_SIZE + 3) {
                writeByte(1)
            }
        }

        assertEquals(PACKET_BUFFER_SIZE + 3, p.remaining)
        p.readFully(ByteArray(PACKET_BUFFER_SIZE - 1))
        assertEquals(0x01010101, p.readInt())
    }

    @Test
    fun testNextBufferBytesStealingFailed() {
        val p = buildPacket {
            repeat(PACKET_BUFFER_SIZE + 1) {
                writeByte(1)
            }
        }

        p.readFully(ByteArray(PACKET_BUFFER_SIZE - 1))

        try {
            p.readInt()
            fail()
        } catch (expected: EOFException) {
        }
    }

    private inline fun buildPacket(block: ByteWritePacket.() -> Unit) = buildPacket(pool, 0, block)
}