package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.channels.ClosedReceiveChannelException
import kotlinx.coroutines.experimental.io.internal.*
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.yield
import org.junit.*
import org.junit.Test
import java.io.IOException
import kotlin.test.*

class ByteBufferChannelScenarioTest : TestBase() {
    private val ch = ByteBufferChannel(true)

    @After
    fun finish() {
        ch.close(InterruptedException())
    }

    @Test
    fun testReadBeforeAvailable() {
        expect(1)

        runBlocking {
            launch(coroutineContext) {
                expect(3)

                val bb = ByteBuffer.allocate(10)
                val rc = ch.readAvailable(bb) // should suspend

                expect(5)
                assertEquals(4, rc)

                expect(6)
            }

            expect(2)
            yield()

            expect(4)
            ch.writeInt(0xff) // should resume

            yield()

            finish(7)
        }
    }

    @Test
    fun testReadBeforeAvailable2() {
        expect(1)

        runBlocking {
            launch(coroutineContext) {
                expect(3)

                val bb = ByteBuffer.allocate(4)
                ch.readFully(bb) // should suspend

                expect(5)

                bb.flip()
                assertEquals(4, bb.remaining())

                expect(6)
            }

            expect(2)
            yield()

            expect(4)
            ch.writeInt(0xff) // should resume

            yield()

            finish(7)
        }
    }

    @Test
    fun testReadAfterAvailable() {
        expect(1)

        runBlocking {
            ch.writeInt(0xff) // should resume

            launch(coroutineContext) {
                expect(3)

                val bb = ByteBuffer.allocate(10)
                val rc = ch.readAvailable(bb) // should NOT suspend

                expect(4)
                assertEquals(4, rc)

                expect(5)
            }

            expect(2)
            yield()

            finish(6)
        }
    }

    @Test
    fun testReadAfterAvailable2() {
        expect(1)

        runBlocking {
            ch.writeInt(0xff) // should resume

            launch(coroutineContext) {
                expect(3)

                val bb = ByteBuffer.allocate(4)
                ch.readFully(bb) // should NOT suspend

                expect(4)
                bb.flip()
                assertEquals(4, bb.remaining())

                expect(5)
            }

            expect(2)
            yield()

            finish(6)
        }
    }

    @Test
    fun testReadToEmpty() {
        runBlocking {
            expect(1)

            val rc = ch.readAvailable(ByteBuffer.allocate(0))

            expect(2)

            assertEquals(0, rc)

            finish(3)
        }
    }

    @Test
    fun testReadToEmptyFromFailedChannel() {
        runBlocking {
            expect(1)

            ch.close(IOException())

            try {
                ch.readAvailable(ByteBuffer.allocate(0))
                fail("Should throw exception")
            } catch (expected: IOException) {
            }

            finish(2)
        }
    }

    @Test
    fun testReadToEmptyFromClosedChannel() {
        runBlocking {
            expect(1)

            ch.close()

            val rc = ch.readAvailable(ByteBuffer.allocate(0))

            expect(2)

            assertEquals(-1, rc)

            finish(3)
        }
    }

    @Test
    fun testReadFullyToEmptyFromClosedChannel() {
        runBlocking {
            expect(1)

            ch.close()

            ch.readFully(ByteBuffer.allocate(0))

            finish(2)
        }
    }

    @Test
    fun testReadFullyFromClosedChannel() {
        runBlocking {
            expect(1)

            ch.close()
            try {
                ch.readFully(ByteBuffer.allocate(1))
                fail("Should throw exception")
            } catch (expected: ClosedReceiveChannelException) {
            }

            finish(2)
        }
    }

    @Test
    fun testReadFullyToEmptyFromFailedChannel() {
        runBlocking {
            expect(1)

            ch.close(IOException())

            try {
                ch.readFully(ByteBuffer.allocate(0))
                fail("Should throw exception")
            } catch (expected: IOException) {
            }

            finish(2)
        }
    }

    @Test
    fun testWriteBlock() {
        runBlocking {
            launch(coroutineContext) {
                expect(1)

                ch.write {
                    it.putLong(0x1234567812345678L)
                }

                expect(2)
            }

            yield()
            expect(3)

            assertEquals(0x1234567812345678L, ch.readLong())
            assertEquals(0, ch.availableForRead)

            finish(4)
        }
    }

    @Test
    fun testWriteBlockSuspend() {
        runBlocking {
            launch(coroutineContext) {
                expect(1)

                ch.writeFully(ByteArray(4088))

                expect(2)

                ch.write(8) {
                    it.putLong(0x1234567812345678L)
                }

                expect(4)
            }

            yield()
            expect(3)

            ch.readFully(ByteArray(9))
            yield()
            expect(5)

            ch.readFully(ByteArray(4088 - 9))

            expect(6)

            assertEquals(0x1234567812345678L, ch.readLong())
            assertEquals(0, ch.availableForRead)

            finish(7)
        }
    }

    @Test
    fun testReadBlock() = runBlocking {
        ch.writeLong(0x1234567812345678L)

        ch.read {
            assertEquals(0x1234567812345678L, it.getLong())
        }

        finish(1)
    }

    @Test
    fun testReadBlockSuspend() = runBlocking {
        ch.writeByte(0x12)

        launch(coroutineContext) {
            expect(1)
            ch.read(8) {
                assertEquals(0x1234567812345678L, it.getLong())
            }

            expect(3)
        }

        yield()
        expect(2)

        ch.writeLong(0x3456781234567800L)
        yield()

        expect(4)
        ch.readByte()
        assertEquals(0, ch.availableForRead)

        finish(5)
    }

    @Test
    fun testReadBlockSuspend2() = runBlocking {
        launch(coroutineContext) {
            expect(1)
            ch.read(8) {
                assertEquals(0x1234567812345678L, it.getLong())
            }

            expect(3)
        }

        yield()
        expect(2)

        ch.writeLong(0x1234567812345678L)
        yield()

        expect(4)
        assertEquals(0, ch.availableForRead)

        finish(5)
    }

    @Test
    fun testWriteByteSuspend() = runBlocking {
        launch(coroutineContext) {
            expect(1)
            ch.writeByte(1)
            ch.writeFully(ByteArray(ch.availableForWrite))
            expect(2)
            ch.writeByte(1)
            expect(5)
            ch.close()
        }

        yield()
        expect(3)
        yield()
        expect(4)
        yield()

        ch.readByte()
        yield()

        ch.readRemaining()
        finish(6)
    }

    @Test
    fun testWriteShortSuspend() = runBlocking {
        launch(coroutineContext) {
            expect(1)
            ch.writeByte(1)
            ch.writeFully(ByteArray(ch.availableForWrite))
            expect(2)
            ch.writeShort(1)
            expect(5)
            ch.close()
        }

        yield()
        expect(3)
        yield()
        expect(4)
        yield()

        ch.readShort()
        yield()

        ch.readRemaining()
        finish(6)
    }

    @Test
    fun testWriteIntSuspend() = runBlocking {
        launch(coroutineContext) {
            expect(1)
            ch.writeByte(1)
            ch.writeFully(ByteArray(ch.availableForWrite))
            expect(2)
            ch.writeInt(1)
            expect(5)
            ch.close()
        }

        yield()
        expect(3)
        yield()
        expect(4)
        yield()

        ch.readInt()
        yield()

        ch.readRemaining()
        finish(6)
    }

    @Test
    fun testWriteIntThenRead() = runBlocking {
        val size = BUFFER_SIZE - RESERVED_SIZE - 3

        expect(1)
        ch.writeFully(java.nio.ByteBuffer.allocate(size))
        ch.flush()
        expect(2)

        launch(coroutineContext) {
            expect(4)
            ch.readPacket(size).release()
        }

        // coroutine is pending
        expect(3)
        ch.writeInt(0x11223344)
        expect(5)

        assertEquals(0x11223344, ch.readInt())

        finish(6)
    }

    @Test
    fun testWriteLongSuspend() = runBlocking {
        launch(coroutineContext) {
            expect(1)
            ch.writeByte(1)
            ch.writeFully(ByteArray(ch.availableForWrite))
            expect(2)
            ch.writeLong(1)
            expect(5)
            ch.close()
        }

        yield()
        expect(3)
        yield()
        expect(4)
        yield()

        ch.readLong()
        yield()

        ch.readRemaining()
        finish(6)
    }

    @Test
    fun testDiscardExisting() = runBlocking {
        launch(coroutineContext) {
            expect(1)
            ch.writeInt(1)
            ch.writeInt(2)
            expect(2)
        }

        yield()
        expect(3)

        assertEquals(4, ch.discard(4))
        assertEquals(2, ch.readInt())

        finish(4)
    }

    @Test
    fun testDiscardPartiallyExisting() = runBlocking {
        ch.writeInt(1)

        launch(coroutineContext) {
            expect(1)
            assertEquals(8, ch.discard(8))
            expect(3)
        }

        yield()
        expect(2)

        ch.writeInt(2)
        yield()

        expect(4)
        assertEquals(0, ch.availableForRead)
        finish(5)
    }

    @Test
    fun testDiscardPartiallyExisting2() = runBlocking {
        launch(coroutineContext) {
            expect(1)
            assertEquals(8, ch.discard(8))
            expect(4)
        }

        yield()

        expect(2)
        ch.writeInt(1)
        yield()
        expect(3)
        assertEquals(0, ch.availableForRead)

        ch.writeInt(2)
        yield()
        expect(5)
        assertEquals(0, ch.availableForRead)
        finish(6)
    }

    @Test
    fun testDiscardClose() = runBlocking {
        launch(coroutineContext) {
            expect(1)
            assertEquals(8, ch.discard())
            expect(4)
        }

        yield()

        expect(2)
        ch.writeInt(1)
        yield()
        ch.writeInt(2)
        yield()

        expect(3)
        ch.close()
        yield()

        finish(5)
    }

    @Test
    fun testWriteWhile() = runBlocking {
        val size = 16384

        launch(coroutineContext) {
            expect(1)
            var b: Byte = 0
            var count = 0

            ch.writeWhile { buffer ->
                while (buffer.hasRemaining() && count < size) {
                    buffer.put(b++)
                    count++
                }
                count < size
            }
            expect(3)
            ch.close()
        }

        yield()

        expect(2)

        val buffer = ByteArray(size)
        ch.readFully(buffer)

        var expectedB: Byte = 0
        for (i in buffer.indices) {
            assertEquals(expectedB, buffer[i])
            expectedB++
        }

        yield()
        yield()

        finish(4)
        assertTrue(ch.isClosedForRead)
    }
}