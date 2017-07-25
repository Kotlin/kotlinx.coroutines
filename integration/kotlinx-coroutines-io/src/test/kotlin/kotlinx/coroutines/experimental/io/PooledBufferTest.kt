package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.io.internal.*
import org.junit.*
import java.nio.*
import java.util.concurrent.*
import kotlin.test.*

class PooledBufferTest {
    private val allocated = CopyOnWriteArrayList<ByteBuffer>()

    private inner class TestPool : ObjectPool<ReadWriteBufferState.Initial> {
        override val capacity: Int get() = 0

        override fun borrow(): ReadWriteBufferState.Initial {
            val buffer = ReadWriteBufferState.Initial(ByteBuffer.allocate(4096), ByteBufferChannel.ReservedSize)
            allocated.add(buffer.backingBuffer)
            return buffer
        }

        override fun recycle(instance: ReadWriteBufferState.Initial) {
            if (!allocated.remove(instance.backingBuffer)) {
                fail("Couldn't release buffer from pool")
            }
        }

        override fun dispose() {
        }
    }

    private val channel = ByteBufferChannel(autoFlush = true, pool = TestPool())

    @After
    fun tearDown() {
        assertTrue { allocated.isEmpty() }
    }

    @Test
    fun testWriteReadClose() {
        runBlocking {
            channel.writeInt(1)
            assertEquals(1, allocated.size)
            channel.readInt()
            channel.close()
            assertEquals(0, allocated.size)
        }
    }

    @Test
    fun testWriteCloseRead() {
        runBlocking {
            channel.writeInt(1)
            assertEquals(1, allocated.size)
            channel.close()
            channel.readInt()
            assertEquals(0, allocated.size)
        }
    }

    @Test
    fun testWriteCloseReadRead() {
        runBlocking {
            channel.writeInt(1)
            assertEquals(1, allocated.size)
            channel.close()
            channel.readShort()
            assertEquals(1, allocated.size)
            channel.readShort()
            assertEquals(0, allocated.size)
        }
    }

    @Test
    fun testCloseOnly() {
        runBlocking {
            channel.close()
            assertEquals(0, allocated.size)
        }
    }
}