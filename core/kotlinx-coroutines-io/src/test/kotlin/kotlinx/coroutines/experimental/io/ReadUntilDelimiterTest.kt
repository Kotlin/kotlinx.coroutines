package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.io.internal.BUFFER_SIZE
import kotlinx.coroutines.experimental.io.internal.asByteBuffer
import org.junit.After
import org.junit.Before
import org.junit.Test
import java.io.IOException
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.test.fail

class ReadUntilDelimiterTest : TestBase() {
    private val source = ByteChannel(true)
    private val nonRepeatingDelimiter = "123".toByteArray().asByteBuffer()
    private val repeatingDelimiter = "AAA".toByteArray().asByteBuffer()

    @Before
    fun setUp() {
        nonRepeatingDelimiter.clear()
        repeatingDelimiter.clear()

//        Thread.sleep(5000)
    }

    @After
    fun tearDown() {
        source.close(CancellationException())
    }

    @Test
    fun testReadUntilDelimiterOnClosed() = runBlocking {
        source.close()
        assertEquals(-1, source.readUntilDelimiter(nonRepeatingDelimiter, ByteBuffer.allocate(100)))
    }

    @Test
    fun testReadUntilDelimiterOnEmptyThenClose() = runBlocking {
        launch(coroutineContext) {
            expect(2)
            source.close()
        }

        expect(1)
        assertEquals(-1, source.readUntilDelimiter(nonRepeatingDelimiter, ByteBuffer.allocate(100)))
        finish(3)
    }

    @Test
    fun smokeTest() = runBlocking {
        val tmp = ByteBuffer.allocate(100)

        source.writeInt(777)
        source.writeFully(nonRepeatingDelimiter.duplicate())
        source.writeInt(999)

        val rc = source.readUntilDelimiter(nonRepeatingDelimiter, tmp)
        assertEquals(4, rc)
        tmp.flip()
        assertEquals(4, tmp.remaining())
        assertEquals(777, tmp.getInt())
        assertEquals(0, nonRepeatingDelimiter.position())
        assertEquals(3, nonRepeatingDelimiter.limit())

        tmp.clear()
        tmp.limit(nonRepeatingDelimiter.remaining())
        source.readFully(tmp)

        source.close()

        tmp.clear()
        val rc2 = source.readUntilDelimiter(nonRepeatingDelimiter, tmp)
        assertEquals(4, rc2)
        tmp.flip()
        assertEquals(4, tmp.remaining())
        assertEquals(999, tmp.getInt())
        tmp.clear()

        val rc3 = source.readUntilDelimiter(nonRepeatingDelimiter, tmp)
        assertEquals(-1, rc3)
    }

    @Test
    fun smokeTestWithRepeatingDelimiter() = runBlocking {
        val tmp = ByteBuffer.allocate(100)

        source.writeInt(777)
        source.writeFully(repeatingDelimiter.duplicate())
        source.writeInt(999)

        val rc = source.readUntilDelimiter(repeatingDelimiter, tmp)
        assertEquals(4, rc)
        tmp.flip()
        assertEquals(4, tmp.remaining())
        assertEquals(777, tmp.getInt())
        assertEquals(0, repeatingDelimiter.position())
        assertEquals(3, repeatingDelimiter.limit())

        tmp.clear()
        tmp.limit(repeatingDelimiter.remaining())
        source.readFully(tmp)

        source.close()

        tmp.clear()
        val rc2 = source.readUntilDelimiter(repeatingDelimiter, tmp)
        assertEquals(4, rc2)
        tmp.flip()
        assertEquals(4, tmp.remaining())
        assertEquals(999, tmp.getInt())
        tmp.clear()

        val rc3 = source.readUntilDelimiter(repeatingDelimiter, tmp)
        assertEquals(-1, rc3)
    }

    @Test
    fun testEnsureSuspendOrder() = runBlocking {
        launch(coroutineContext) {
            expect(2)
            source.writeInt(777)
            yield()
            expect(3)
            source.writeInt(999)
            yield()
            expect(4)
            source.writeFully(nonRepeatingDelimiter.duplicate())
        }

        expect(1)
        val tmp = ByteBuffer.allocate(100)
        val rc = source.readUntilDelimiter(nonRepeatingDelimiter, tmp)
        expect(5)

        assertEquals(8, rc)
        tmp.flip()
        assertEquals(777, tmp.getInt())
        assertEquals(999, tmp.getInt())
        tmp.clear()

        expect(6)

        assertEquals(0, source.readUntilDelimiter(nonRepeatingDelimiter, tmp))

        source.skipDelimiter(nonRepeatingDelimiter)

        source.close()
        assertEquals(-1, source.readUntilDelimiter(nonRepeatingDelimiter, tmp))


        finish(7)
    }

    @Test
    fun testBulkWrite() = runBlocking {
        launch(coroutineContext) {
            expect(2)

            val buffer = ByteBuffer.allocate(100)
            buffer.putInt(777)
            buffer.putInt(999)
            buffer.put(nonRepeatingDelimiter.duplicate())
            buffer.flip()

            source.writeFully(buffer)
        }

        expect(1)
        val tmp = ByteBuffer.allocate(100)
        val rc = source.readUntilDelimiter(nonRepeatingDelimiter, tmp)
        expect(3)

        assertEquals(8, rc)
        tmp.flip()
        assertEquals(777, tmp.getInt())
        assertEquals(999, tmp.getInt())
        tmp.clear()

        expect(4)

        assertEquals(0, source.readUntilDelimiter(nonRepeatingDelimiter, tmp))

        finish(5)
    }

    @Test
    fun testPartitionedDelimiter() = runBlocking {
        launch(coroutineContext) {
            expect(2)

            val buffer = ByteBuffer.allocate(100)
            buffer.putInt(777)
            buffer.putInt(999)
            buffer.put(nonRepeatingDelimiter.duplicate().apply { limit(1) })
            buffer.flip()

            source.writeFully(buffer)

            yield()
            expect(3)

            source.writeFully(nonRepeatingDelimiter.duplicate().apply { position(1) })
            source.close()
        }

        expect(1)
        val tmp = ByteBuffer.allocate(100)
        val rc = source.readUntilDelimiter(nonRepeatingDelimiter, tmp)
        expect(4)

        assertEquals(8, rc)
        tmp.flip()
        assertEquals(777, tmp.getInt())
        assertEquals(999, tmp.getInt())
        tmp.clear()

        expect(5)

        assertEquals(0, source.readUntilDelimiter(nonRepeatingDelimiter, tmp))
        source.skipDelimiter(nonRepeatingDelimiter)
        assertEquals(-1, source.readUntilDelimiter(nonRepeatingDelimiter, tmp))


        finish(6)
    }

    @Test
    fun testReadUntilDelimiterWrapped() = runBlocking {
        val padSize = BUFFER_SIZE - 8 - 1

        launch(coroutineContext) {
            expect(2)
            source.writeFully(ByteBuffer.allocate(padSize - 1))
            source.writeByte(99)
            yield()

            expect(4)
            source.writeFully(nonRepeatingDelimiter.duplicate())
            expect(5)
        }

        expect(1)
        source.readFully(ByteBuffer.allocate(padSize - 1))
        expect(3)

        val tmp = ByteBuffer.allocate(100)
        val rc = source.readUntilDelimiter(nonRepeatingDelimiter, tmp)
        assertEquals(1, rc)
        assertEquals(99, tmp.get(0).toInt())

        finish(6)
    }

    @Test
    fun testReadUntilDelimiterRepeatedWrapped() = runBlocking {
        val padSize = BUFFER_SIZE - 8 - 1

        launch(coroutineContext) {
            expect(2)
            source.writeFully(ByteBuffer.allocate(padSize - 1))
            source.writeByte(99)
            yield()

            expect(4)
            source.writeFully(repeatingDelimiter.duplicate())
            expect(5)
        }

        expect(1)
        source.readFully(ByteBuffer.allocate(padSize - 1))
        expect(3)

        val tmp = ByteBuffer.allocate(100)
        val rc = source.readUntilDelimiter(repeatingDelimiter, tmp)
        assertEquals(1, rc)
        assertEquals(99, tmp.get(0).toInt())

        finish(6)
    }

    @Test
    fun testReadUntilDelimiterPartialFailure() = runBlocking {
        val padSize = BUFFER_SIZE - 8 - 1

        launch(coroutineContext) {
            expect(2)
            source.writeFully(ByteBuffer.allocate(padSize - 1))
            source.writeByte(99)
            yield()

            expect(4)
            source.writeByte(repeatingDelimiter.get(0))
            source.writeByte(999)
            expect(5)

            yield()
            expect(6)
            source.close()
        }

        expect(1)
        source.readFully(ByteBuffer.allocate(padSize - 1))
        expect(3)

        val tmp = ByteBuffer.allocate(100)
        val rc = source.readUntilDelimiter(repeatingDelimiter, tmp)
        expect(7)
        assertEquals(3, rc)
        assertEquals(99, tmp.get(0).toInt())

        finish(8)
    }

    @Test
    fun testReadUntilDelimiterPartialFailure2() = runBlocking {
        val padSize = BUFFER_SIZE - 8 - 1

        launch(coroutineContext) {
            expect(2)
            source.writeFully(ByteBuffer.allocate(padSize - 1))
            source.writeByte(99)
            yield()

            expect(4)
            source.writeByte(repeatingDelimiter.get(0))
            source.writeByte(88)
            source.writeByte(77)
            expect(5)

            yield()
            expect(6)
            source.close()
        }

        expect(1)
        source.readFully(ByteBuffer.allocate(padSize - 1))
        expect(3)

        val tmp = ByteBuffer.allocate(100)
        val rc = source.readUntilDelimiter(repeatingDelimiter, tmp)
        expect(7)
        assertEquals(4, rc)
        tmp.flip()
        assertEquals(99, tmp.get().toInt())
        assertEquals(repeatingDelimiter.get(0), tmp.get())
        assertEquals(88, tmp.get().toInt())
        assertEquals(77, tmp.get().toInt())

        finish(8)
    }

    @Test
    fun testReadUntilDelimiterWrappedNotEnoughThenFailure() = runBlocking {
        val padSize = BUFFER_SIZE - 8 - 1

        launch(coroutineContext) {
            expect(2)
            source.writeFully(ByteBuffer.allocate(padSize - 1))
            source.writeByte(99)
            yield()

            expect(4)
            assertTrue { repeatingDelimiter.remaining() > 2 }
            source.writeFully(repeatingDelimiter.duplicate().apply { limit(limit() - 1) })
            expect(5)

            yield()
            expect(6)
            source.close()
        }

        expect(1)
        source.readFully(ByteBuffer.allocate(padSize - 1))
        expect(3)

        val tmp = ByteBuffer.allocate(100)
        val rc = source.readUntilDelimiter(repeatingDelimiter, tmp)
        expect(7)
        assertEquals(3, rc)
        tmp.flip()
        assertEquals(99, tmp.get().toInt())
        for (i in 0 until repeatingDelimiter.remaining() - 1) {
            assertEquals(repeatingDelimiter.get(i), tmp.get())
        }

        finish(8)
    }

    @Test
    fun testSkipDelimiterSuspend() = runBlocking {
        launch(coroutineContext) {
            expect(2)
            source.writeFully(nonRepeatingDelimiter.duplicate())
        }

        expect(1)
        source.skipDelimiter(nonRepeatingDelimiter)
        finish(3)
    }

    @Test
    fun testSkipDelimiterFullyAvailable() = runBlocking {
        launch(coroutineContext) {
            expect(2)
            source.writeFully(nonRepeatingDelimiter.duplicate())
            expect(3)
        }

        expect(1)
        yield()
        expect(4)
        source.skipDelimiter(nonRepeatingDelimiter)
        finish(5)
    }

    @Test
    fun testSkipDelimiterSuspendMultiple() = runBlocking {
        launch(coroutineContext) {
            expect(2)
            source.writeFully(nonRepeatingDelimiter.duplicate().apply { limit(1) })
            yield()
            expect(3)
            source.writeFully(nonRepeatingDelimiter.duplicate().apply { position(1) })
        }

        expect(1)
        yield()
        source.skipDelimiter(nonRepeatingDelimiter)
        finish(4)
    }

    @Test
    fun testSkipDelimiterSuspendRingBufferWrap() = runBlocking {
        launch(coroutineContext) {
            expect(2)
            source.writeFully(ByteBuffer.allocate(BUFFER_SIZE - 9))
            yield()

            expect(4)
            source.writeFully(nonRepeatingDelimiter.duplicate())
            yield()
        }

        expect(1)
        source.readFully(ByteBuffer.allocate(BUFFER_SIZE - 9))
        expect(3)

        source.skipDelimiter(nonRepeatingDelimiter)
        finish(5)
    }

    @Test
    fun testSkipDelimiterBroken() = runBlocking {
        launch(coroutineContext) {
            expect(2)
            val bb = ByteBuffer.allocate(nonRepeatingDelimiter.remaining())
            bb.put(nonRepeatingDelimiter.duplicate())
            bb.put(1, (bb.get(1) + 1).toByte())
            bb.clear()
            source.writeFully(bb)
            expect(3)
        }

        expect(1)
        yield()
        expect(4)

        try {
            source.skipDelimiter(nonRepeatingDelimiter)
            fail()
        } catch (expected: IOException) {
        }

        finish(5)
    }


}