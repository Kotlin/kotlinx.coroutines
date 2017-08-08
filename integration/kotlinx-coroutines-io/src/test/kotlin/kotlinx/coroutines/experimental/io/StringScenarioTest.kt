package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import org.junit.*
import kotlin.test.*

class StringScenarioTest : TestBase() {
    private val ch = ByteBufferChannel(autoFlush = true)

    @Test
    fun testWriteCharByChar() {
        runBlocking {
            expect(1)

            launch(coroutineContext) {
                ch.writeStringUtf8("A")
                expect(3)
                yield()

                expect(5)
                ch.writeStringUtf8("B")
                expect(6)
                yield()

                expect(7)
                ch.writeStringUtf8("\n")
                expect(8)
                yield()
            }

            expect(2)
            yield()

            expect(4)
            val line = ch.readUTF8Line()

            assertEquals("AB", line)
            expect(9)

            yield()
            expect(10)
            finish(11)
        }
    }

    @Test
    fun testSplitUtf8() {
        runBlocking {
            val sb = StringBuilder()

            expect(1)

            launch(coroutineContext) {
                expect(2)
                val b = byteArrayOf(0xd0.toByte(), 0x9a.toByte(), 0x0a)
                ch.writeFully(b, 0, 1)
                yield()

                expect(3)
                assertTrue { sb.isEmpty() }

                ch.writeFully(b, 1, 1)
                yield()

                expect(4)
                assertEquals("\u041a", sb.toString())

                ch.writeFully(b, 2, 1)
                yield()
            }

            ch.readUTF8LineTo(sb)
            expect(5)

            assertEquals("\u041a", sb.toString())

            finish(6)
        }
    }

    @Test
    fun testSplitLineDelimiter() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)
            ch.writeFully("ABC\r".toByteArray())
            expect(3)
            yield()

            expect(5)
            ch.writeFully("\n".toByteArray())
            yield()
        }

        yield()

        expect(4)
        val line = ch.readASCIILine()
        expect(6)

        assertEquals("ABC", line)

        finish(7)
    }

    @Test
    fun testReadTailWriteFirst() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(2)

            ch.writeFully("ABC".toByteArray())

            yield()

            expect(4)
            ch.close()
            yield()
        }

        yield()

        expect(3)

        val line = ch.readUTF8Line()
        expect(5)
        assertEquals("ABC", line)

        finish(6)
    }

    @Test
    fun testReadTailReadFirst() = runBlocking {
        expect(1)

        launch(coroutineContext) {
            expect(3)

            ch.writeFully("ABC".toByteArray())

            yield()

            expect(4)
            ch.close()
            yield()
        }

        expect(2)

        val line = ch.readUTF8Line()
        expect(5)
        assertEquals("ABC", line)

        finish(6)
    }

    @Test
    fun testReadThroughWrap() = runBlocking {
        val L = ".".repeat(128)

        expect(1)

        launch(coroutineContext) {
            expect(2)

            ch.writeFully(ByteArray(4000))

            expect(3)
            ch.readFully(ByteArray(3999)) // keep one byte remaining to keep buffer unreleased

            expect(4)

            ch.writeFully(L.toByteArray())

            expect(5)
            ch.close()
        }

        yield()

        expect(6)

        ch.readByte()
        expect(7)

        val line = ch.readUTF8Line()

        finish(8)

        assertEquals(L, line)
    }

    @Test
    fun testReadShifted() = runBlocking {
        val L = ".".repeat(127) + "\n"
        var base = 0

        for (shift in 1..4096 - 8) {
            expect(base + 1)

            launch(coroutineContext) {
                expect(base + 2)

                ch.writeFully(ByteArray(shift))

                expect(base + 3)
                ch.readFully(ByteArray(shift - 1)) // keep one byte remaining to keep buffer unreleased

                expect(base + 4)

                ch.writeFully(L.toByteArray())

                expect(base + 5)
            }

            yield()

            expect(base + 6)

            ch.readByte()
            expect(base + 7)

            val line = ch.readUTF8Line()

            expect(base + 8)

            assertEquals(L.dropLast(1), line)

            base += 8
        }

        finish(base + 1)
    }

    @Test
    fun writeLongLine() = runBlocking {
        val L = ".".repeat(16384)

        expect(1)

        launch(coroutineContext) {
            expect(2)

            ch.writeFully(L.toByteArray())

            expect(4)
            ch.close()
        }

        yield()

        expect(3)
        val line = ch.readUTF8Line()

        expect(5)

        assertEquals(L, line)

        finish(6)
    }
}