package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.packet.*
import org.junit.*
import java.util.*
import kotlin.test.*

class BytePacketReaderWriterTest {
    @Test
    fun testReaderEmpty() {
        val packet = buildPacket {
        }

        assertEquals(-1, packet.readerUTF8().read())
    }

    @Test
    fun testReaderFew() {
        val packet = buildPacket {
            append("ABC")
        }

        assertEquals("ABC", packet.readerUTF8().readText())
    }

    @Test
    fun testReaderMultiple() {
        val s = buildString {
            repeat(100000) {
                append("e")
            }
        }

        val packet = buildPacket {
            append(s)
        }

        assertEquals(s, packet.readerUTF8().readText())
    }

    @Test
    fun testReaderFewUtf() {
        val s = "\u0447"
        val packet = buildPacket {
            append(s)
        }

        assertEquals(s, packet.readerUTF8().readText())
    }

    @Test
    fun testReaderFewUtf3bytes() {
        val s = "\u0BF5"
        val packet = buildPacket {
            append(s)
        }

        assertEquals(s, packet.readerUTF8().readText())
    }

    @Test
    fun testReaderMultipleUtf() {
        val s = buildString {
            repeat(100000) {
                append("\u0447")
            }
        }

        val packet = buildPacket {
            append(s)
        }

        assertEquals(s, packet.readerUTF8().readText())
    }

    @Test
    fun testReaderMultipleUtf3bytes() {
        val s = buildString {
            repeat(100000) {
                append("\u0BF5")
            }
        }

        val packet = buildPacket {
            append(s)
        }

        assertEquals(s, packet.readerUTF8().readText())
    }

    @Test
    fun testWriterSingleBufferSingleWrite() {
        val s = buildString {
            append("ABC")
        }

        val packet = buildPacket {
            writerUTF8().write(s)
        }

        assertEquals(s, packet.inputStream().readBytes().toString(Charsets.UTF_8))
    }

    @Test
    fun testWriterSingleBufferSingleWriteUtf() {
        val s = buildString {
            append("A\u0447C")
        }

        val packet = buildPacket {
            writerUTF8().write(s)
        }

        assertEquals(s, packet.inputStream().readBytes().toString(Charsets.UTF_8))
    }

    @Test
    fun testWriterSingleBufferMultipleWrite() {
        val s = buildString {
            append("ABC")
        }

        val packet = buildPacket {
            writerUTF8().apply {
                write(s.substring(0, 1))
                write(s.substring(1))
            }
        }

        assertEquals(s, packet.inputStream().readBytes().toString(Charsets.UTF_8))
    }

    @Test
    fun testWriterSingleBufferMultipleWriteUtf() {
        val s = buildString {
            append("\u0447BC")
            append("A\u0447C")
            append("AB\u0447")
            append("\u0447")
        }

        val packet = buildPacket {
            writerUTF8().let { w ->
                w.write("\u0447BC")
                w.write("A\u0447C")
                w.write("AB\u0447")
                w.write("\u0447")
            }
        }

        assertEquals(s, packet.inputStream().readBytes().toString(Charsets.UTF_8))
    }

    @Test
    fun testWriterMultiBufferSingleWrite() {
        val s = buildString {
            repeat(100000) {
                append("x")
            }
        }

        val packet = buildPacket {
            writerUTF8().write(s)
        }

        assertEquals(s, packet.inputStream().readBytes().toString(Charsets.UTF_8))
    }

    @Test
    fun testWriterMultiBufferSingleWriteUtf() {
        val s = buildString {
            repeat(100000) {
                append("A\u0447")
            }
        }

        val packet = buildPacket {
            writerUTF8().write(s)
        }

        assertEquals(s, packet.inputStream().readBytes().toString(Charsets.UTF_8))
    }

    @Test
    fun testWriterMultiBufferSingleWriteUtf3bytes() {
        val s = buildString {
            repeat(100000) {
                append("\u0BF5")
            }
        }

        val packet = buildPacket {
            writerUTF8().write(s)
        }

        assertEquals(s, packet.inputStream().readBytes().toString(Charsets.UTF_8))
    }

    @Test
    fun testReadLineSingleBuffer() {
        val p = buildPacket {
            append("1\r22\n333\r\n4444")
        }

        assertEquals("1", p.readUTF8Line())
        assertEquals("22", p.readUTF8Line())
        assertEquals("333", p.readUTF8Line())
        assertEquals("4444", p.readUTF8Line())
        assertNull(p.readUTF8Line())
    }

    @Test
    fun testReadLineMutiBuffer() {
        val p = buildPacket {
            repeat(1000) {
                append("1\r22\n333\r\n4444\n")
            }
        }

        repeat(1000) {
            assertEquals("1", p.readUTF8Line())
            assertEquals("22", p.readUTF8Line())
            assertEquals("333", p.readUTF8Line())
            assertEquals("4444", p.readUTF8Line())
        }

        assertNull(p.readUTF8Line())
    }

    @Test
    fun testSingleBufferReadText() {
        val p = buildPacket {
            append("ABC")
        }

        assertEquals("ABC", p.readText().toString())
    }

    @Test
    fun testMultiBufferReadText() {
        val s = buildString {
            repeat(100000) {
                append("x")
            }
        }

        val packet = buildPacket {
            writeFully(s.toByteArray())
        }

        assertEquals(s, packet.readText().toString())
    }

    @Test
    fun testSingleBufferReadAll() {
        val bb = ByteArray(100)
        Random().nextBytes(bb)

        val p = buildPacket {
            writeFully(bb)
        }

        assertTrue { bb.contentEquals(p.readBytes()) }
    }

    @Test
    fun testMultiBufferReadAll() {
        val bb = ByteArray(100000)
        Random().nextBytes(bb)

        val p = buildPacket {
            writeFully(bb)
        }

        assertTrue { bb.contentEquals(p.readBytes()) }
    }
}