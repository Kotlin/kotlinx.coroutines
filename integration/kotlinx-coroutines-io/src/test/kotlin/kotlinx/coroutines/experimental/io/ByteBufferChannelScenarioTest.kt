package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import org.junit.*
import java.io.*
import kotlin.test.*

class ByteBufferChannelScenarioTest : TestBase() {
    private val ch = ByteBufferChannel(true)

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
}