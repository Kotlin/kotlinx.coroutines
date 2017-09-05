package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.io.internal.*
import org.junit.*
import kotlin.test.*

class ReadUntilDelimiterTest : TestBase() {
    private val source = ByteChannel(true)
    private val nonRepeatingDelimiter = "123".toByteArray().asByteBuffer()
    private val repeatingDelimiter = "AAA".toByteArray().asByteBuffer()

    @Before
    fun setUp() {
//        Thread.sleep(5000)
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
        assertEquals(0, rc3)
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
        assertEquals(0, rc3)
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

        finish(6)
    }
}