package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.buffers.*
import kotlinx.coroutines.experimental.io.packet.*
import org.junit.*
import java.util.*
import kotlin.test.*

class BytePacketReaderWriterTest {
    @get:Rule
    private val pool = VerifyingObjectPool(BufferView.Pool)

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

    @Test
    fun testCopySingleBufferPacket() {
        val bb = ByteArray(100)
        Random().nextBytes(bb)

        val p = buildPacket {
            writeFully(bb)
        }

        val copy = p.copy()
        assertEquals(p.remaining, p.remaining)
        assertTrue { p.readBytes().contentEquals(copy.readBytes()) }
    }

    @Test
    fun testCopyMultipleBufferPacket() {
        val bb = ByteArray(1000000)
        Random().nextBytes(bb)

        val p = buildPacket {
            writeFully(bb)
        }

        val copy = p.copy()
        assertEquals(p.remaining, p.remaining)
        val bytes = p.readBytes()
        val copied = copy.readBytes()

        assertTrue { bytes.contentEquals(copied) }
    }

    @Test
    fun testWritePacketSingle() {
        val inner = buildPacket {
            append("ABC")
        }

        val outer = buildPacket {
            append("123")
            assertEquals(3, size)
            writePacket(inner)
            assertEquals(6, size)
            append(".")
        }

        assertEquals("123ABC.", outer.readText().toString())
        assertEquals(0, inner.remaining)
    }

    @Test
    fun testWritePacketMultiple() {
        val inner = buildPacket {
            append("o".repeat(100000))
        }

        val outer = buildPacket {
            append("123")
            assertEquals(3, size)
            writePacket(inner)
            assertEquals(100003, size)
            append(".")
        }

        assertEquals("123" + "o".repeat(100000) + ".", outer.readText().toString())
        assertEquals(0, inner.remaining)
    }

    @Test
    fun writePacketWithHintExact() {
        val inner = buildPacket(pool, 4) {
            append(".")
        }

        val outer = buildPacket {
            append("1234")
            assertEquals(4, size)
            writePacket(inner)
            assertEquals(5, size)
        }

        assertEquals("1234.", outer.readText().toString())
        assertEquals(0, inner.remaining)
    }

    @Test
    fun writePacketWithHintBigger() {
        val inner = buildPacket(pool, 10) {
            append(".")
        }

        val outer = buildPacket {
            append("1234")
            assertEquals(4, size)
            writePacket(inner)
            assertEquals(5, size)
        }

        assertEquals("1234.", outer.readText().toString())
        assertEquals(0, inner.remaining)
    }

    @Test
    fun writePacketWithHintFailed() {
        val inner = buildPacket(pool, 3) {
            append(".")
        }

        val outer = buildPacket {
            append("1234")
            assertEquals(4, size)
            writePacket(inner)
            assertEquals(5, size)
        }

        assertEquals("1234.", outer.readText().toString())
        assertEquals(0, inner.remaining)
    }

    @Test
    fun testWritePacketSingleUnconsumed() {
        val inner = buildPacket {
            append("ABC")
        }

        val outer = buildPacket {
            append("123")
            assertEquals(3, size)
            writePacket(inner.copy())
            assertEquals(6, size)
            append(".")
        }

        assertEquals("123ABC.", outer.readText().toString())
        assertEquals(3, inner.remaining)
    }

    @Test
    fun testWritePacketMultipleUnconsumed() {
        val inner = buildPacket {
            append("o".repeat(100000))
        }

        val outer = buildPacket {
            append("123")
            assertEquals(3, size)
            writePacket(inner.copy())
            assertEquals(100003, size)
            append(".")
        }

        assertEquals("123" + "o".repeat(100000) + ".", outer.readText().toString())
        assertEquals(100000, inner.remaining)
    }

    @Test
    fun testWriteDirect() {
        val packet = buildPacket {
            writeDirect { bb ->
                bb.putLong(0x1234567812345678L)
            }
        }

        assertEquals(0x1234567812345678L, packet.readLong())
    }

    private inline fun buildPacket(block: ByteWritePacket.() -> Unit) = buildPacket(pool, 0, block)
}