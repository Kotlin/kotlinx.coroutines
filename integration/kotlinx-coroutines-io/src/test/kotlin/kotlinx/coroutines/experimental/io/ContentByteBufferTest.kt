package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import org.junit.*
import java.nio.*
import java.util.*
import kotlin.test.*

class ContentByteBufferTest {
    @Test
    fun testEmptyContent() = runBlocking {
        val ch = ByteBufferChannel(ByteArray(0))
        assertEquals(0, ch.remaining)
        assertEquals(-1, ch.readLazy(ByteBuffer.allocate(100)))
        assertTrue { ch.isClosedForReceive }
    }

    @Test
    fun testSingleByteContent() = runBlocking {
        val ch = ByteBufferChannel(byteArrayOf(1))
        assertEquals(1, ch.remaining)
        assertFalse { ch.isClosedForReceive }
        assertEquals(1, ch.readLazy(ByteBuffer.allocate(100)))
        assertEquals(0, ch.remaining)
        assertTrue { ch.isClosedForReceive }
    }

    @Test
    fun testSingleByteContent2() = runBlocking {
        val ch = ByteBufferChannel(byteArrayOf(0x34))
        assertEquals(1, ch.remaining)
        assertFalse { ch.isClosedForReceive }
        assertEquals(0x34, ch.readByte())
        assertEquals(0, ch.remaining)
        assertTrue { ch.isClosedForReceive }
    }

    @Test
    fun testMultipleByteContent2() = runBlocking {
        val arr = ByteArray(16)
        Random().nextBytes(arr)
        val ch = ByteBufferChannel(arr)

        assertEquals(16, ch.remaining)
        assertFalse { ch.isClosedForReceive }
        ch.readByte()
        ch.readShort()
        ch.readInt()
        ch.readLong()
        ch.readByte()
        assertTrue { ch.isClosedForReceive }
    }
}