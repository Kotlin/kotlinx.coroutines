package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.packet.*
import org.junit.*
import kotlin.test.*

class BytePacketBuildTest {
    @Test
    fun smokeSingleBufferTest() {
        val p = buildPacket {
            writeByte(0x12)
            writeShort(0x1234)
            writeInt(0x12345678)
            writeDouble(1.23)
            writeFloat(1.23f)
            writeLong(0x123456789abcdef0)

            writeStringUtf8("OK\n")
            listOf(1, 2, 3).joinTo(this, separator = "|")
        }

        assertEquals(1 + 2 + 4 + 8 + 4 + 8 + 3 + 5, p.remaining)

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
            writeByte(0x12)
            writeShort(0x1234)
            writeInt(0x12345678)
            writeDouble(1.23)
            writeFloat(1.23f)
            writeLong(0x123456789abcdef0)

            writeStringUtf8("OK\n")
            listOf(1, 2, 3).joinTo(this, separator = "|")
        }

        assertEquals(9999 + 1 + 2 + 4 + 8 + 4 + 8 + 3 + 5, p.remaining)

        p.readFully(ByteArray(9999))
        assertEquals(0x12, p.readByte())
        assertEquals(0x1234, p.readShort())
        assertEquals(0x12345678, p.readInt())
        assertEquals(1.23, p.readDouble())
        assertEquals(1.23f, p.readFloat())
        assertEquals(0x123456789abcdef0, p.readLong())

        assertEquals("OK", p.readUTF8Line())
        assertEquals("1|2|3", p.readUTF8Line())
    }
}