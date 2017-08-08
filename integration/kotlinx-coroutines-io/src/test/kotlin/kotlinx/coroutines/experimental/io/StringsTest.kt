package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.rules.*
import java.nio.*
import java.util.*
import java.util.concurrent.*
import kotlin.test.*

class StringsTest {
    @get:Rule
    val timeout = Timeout(10, TimeUnit.SECONDS)

    private val channel = ByteBufferChannel(autoFlush = true)

    @Test
    fun testReadString() {
        runBlocking {
            writeString("Hello, World!")
            channel.close()
            assertEquals("Hello, World!", channel.readASCIILine())
        }
    }

    @Test
    fun testReadLines() {
        runBlocking {
            writeString("Hello, World!\nLine2")
            assertEquals("Hello, World!", channel.readASCIILine())
            channel.close()
            assertEquals("Line2", channel.readASCIILine())
        }
    }

    @Test
    fun testReadASCIILineLf() {
        runBlocking {
            writeParts("A", "B\n", "C")

            assertEquals("AB", channel.readASCIILine())
            assertEquals("C", channel.readASCIILine())
            assertEquals(null, channel.readASCIILine())
        }
    }

    @Test
    fun testReadASCIILineCrLf() {
        runBlocking {
            writeParts("A", "B\r\n", "C")

            assertEquals("AB", channel.readASCIILine())
            assertEquals("C", channel.readASCIILine())
            assertEquals(null, channel.readASCIILine())
        }
    }

    @Test
    fun testReadASCIILineCrLfBadSplit() {
        runBlocking {
            writeParts("A", "B\r", "\nC")

            assertEquals("AB", channel.readASCIILine())
            assertEquals("C", channel.readASCIILine())
            assertEquals(null, channel.readASCIILine())
        }
    }

    @Test
    fun testReadASCIILineTrailingLf() {
        runBlocking {
            writeParts("A", "B\n", "C\n")

            assertEquals("AB", channel.readASCIILine())
            assertEquals("C", channel.readASCIILine())
            assertEquals(null, channel.readASCIILine())
        }
    }

    @Test
    fun testReadASCIILineLeadingLf() {
        runBlocking {
            writeParts("\nA", "B\n", "C")

            assertEquals("", channel.readASCIILine())
            assertEquals("AB", channel.readASCIILine())
            assertEquals("C", channel.readASCIILine())
            assertEquals(null, channel.readASCIILine())
        }
    }

    @Test
    fun testLookAhead() {
        val text = buildString() {
            for (i in 0 until 65535) {
                append((i and 0xf).toString(16))
            }
        }.toByteArray()

        runBlocking {
            launch(CommonPool) {
                channel.writeFully(text)
                channel.close()
            }

            val comparison = ByteBuffer.wrap(text)

            val arr = ByteArray(128)
            var rem = text.size
            val rnd = Random()

            while (rem > 0) {
                val s = rnd.nextInt(arr.size).coerceIn(1, rem)
                arr.fill(0)
                val rc = channel.readLazy(arr, 0, s)

                if (rc == -1) fail("EOF")

                val actual = String(arr, 0, rc)

                val expectedBytes = ByteArray(rc)
                comparison.get(expectedBytes)
                val expected = expectedBytes.toString(Charsets.ISO_8859_1)

                assertEquals(expected, actual)

                rem -= rc
            }
        }
    }

    @Test
    fun testLongLinesConcurrent() {
        val lines = (0..1024).map { size ->
            buildString(size) {
                for (i in 0 until size) {
                    append((i and 0xf).toString(16))
                }
            }
        }

        runBlocking {
            launch(CommonPool) {
                for (part in lines) {
                    writeString(part + "\n")
                }
                channel.close()
            }

            for (expected in lines) {
                assertEquals(expected, channel.readASCIILine(expected.length))
            }

            assertNull(channel.readASCIILine())
        }
    }

    @Test
    fun testLongLinesSequential() {
        val lines = (0..1024).map { size ->
            buildString(size) {
                for (i in 0 until size) {
                    append((i and 0xf).toString(16))
                }
            }
        }

        runBlocking {
            launch(coroutineContext) {
                for (part in lines) {
                    writeString(part + "\n")
                    yield()
                }
                channel.close()
            }

            for (expected in lines) {
                Thread.yield()
                assertEquals(expected, channel.readASCIILine(expected.length))
            }

            assertNull(channel.readASCIILine())
        }
    }

    @Test
    fun testReadUTF8Line2bytes() {
        val parts = byteArrayOf(0xd0.toByte(), 0x9a.toByte(), 0x0a)

        runBlocking {
            channel.writeFully(parts)
            assertEquals("\u041a", channel.readUTF8Line())
        }
    }

    @Test
    fun testReadUTF8Line3bytes() {
        val parts = byteArrayOf(0xe0.toByte(), 0xaf.toByte(), 0xb5.toByte(), 0x0a)

        runBlocking {
            channel.writeFully(parts)
            assertEquals("\u0BF5", channel.readUTF8Line())
        }
    }

    @Test
    fun testReadUTF8Line4bytes() {
        val parts = byteArrayOf(0xF0.toByte(), 0xA6.toByte(), 0x88.toByte(), 0x98.toByte(), 0x0a)

        runBlocking {
            channel.writeFully(parts)
            assertEquals("\uD858\uDE18", channel.readUTF8Line())
        }
    }

    private suspend fun writeString(s: String) {
        channel.writeFully(s.toByteArray(Charsets.ISO_8859_1))
    }

    private fun writeParts(vararg parts: String) {
        launch(CommonPool) {
            parts.forEach { p ->
                writeString(p)
                yield()
                delay(1)
            }

            channel.close()
        }
    }
}