package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.*
import org.junit.Test
import java.util.*
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class ContentByteBufferTest : TestBase() {
    @Test
    fun testEmptyContent() = runBlocking {
        val ch = ByteReadChannel(ByteArray(0))
        assertEquals(0, ch.availableForRead)
        assertEquals(-1, ch.readAvailable(ByteBuffer.allocate(100)))
        assertTrue { ch.isClosedForRead }
    }

    @Test
    fun testSingleByteContent() = runBlocking {
        val ch = ByteReadChannel(byteArrayOf(1))
        assertEquals(1, ch.availableForRead)
        assertFalse { ch.isClosedForRead }
        assertEquals(1, ch.readAvailable(ByteBuffer.allocate(100)))
        assertEquals(0, ch.availableForRead)
        assertTrue { ch.isClosedForRead }
    }

    @Test
    fun testSingleByteContent2() = runBlocking {
        val ch = ByteReadChannel(byteArrayOf(0x34))
        assertEquals(1, ch.availableForRead)
        assertFalse { ch.isClosedForRead }
        assertEquals(0x34, ch.readByte())
        assertEquals(0, ch.availableForRead)
        assertTrue { ch.isClosedForRead }
    }

    @Test
    fun testMultipleByteContent2() = runBlocking {
        val arr = ByteArray(16)
        Random().nextBytes(arr)
        val ch = ByteReadChannel(arr)
        assertEquals(16, ch.availableForRead)
        assertFalse { ch.isClosedForRead }
        ch.readByte()
        ch.readShort()
        ch.readInt()
        ch.readLong()
        ch.readByte()
        assertTrue { ch.isClosedForRead }
    }
}