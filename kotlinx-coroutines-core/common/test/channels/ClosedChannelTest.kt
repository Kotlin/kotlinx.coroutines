package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlin.test.*

class ClosedChannelTest : TestBase() {
    /**
     * Iterator.
     */

    @Test
    fun testIteratorClosedHasNextFalse() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            val iterator = channel.iterator()
            channel.close()
            assertFalse(iterator.hasNext())
        }
    }

    @Test
    fun testIteratorClosedWithExceptionHasNextThrows() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            val iterator = channel.iterator()
            channel.close(TestException())
            assertFailsWith<TestException> { (iterator.hasNext()) }
        }
    }

    /**
     * Properties.
     *
     * Properties stay the same regardless of whether the channel was closed with or without exception.
     */

    @Test
    fun testClosedIsClosedForReceive() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            assertFalse(channel.isClosedForReceive)
            channel.close()
            assertTrue(channel.isClosedForReceive)
        }
    }

    @Test
    fun testClosedWithExceptionIsClosedForReceive() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            assertFalse(channel.isClosedForReceive)
            channel.close(TestException())
            assertTrue(channel.isClosedForReceive)
        }
    }

    @Test
    fun testClosedIsEmptyFalse() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            assertTrue(channel.isEmpty)
            assertFalse(channel.isClosedForReceive)
            channel.close()
            // NB! Not obvious.
            assertFalse(channel.isEmpty)
            assertTrue(channel.isClosedForReceive)
        }
    }

    @Test
    fun testClosedWithExceptionIsEmptyFalse() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            assertTrue(channel.isEmpty)
            assertFalse(channel.isClosedForReceive)
            channel.close(TestException())
            assertFalse(channel.isEmpty)
            assertTrue(channel.isClosedForReceive)
        }
    }

    @Test
    fun testSendClosedReceiveIsEmptyFalse() = runTest {
        val channel = Channel<Int>(1)
        assertTrue(channel.isEmpty)
        assertFalse(channel.isClosedForReceive)
        channel.send(1)
        assertFalse(channel.isEmpty)
        assertFalse(channel.isClosedForReceive)
        channel.close()
        assertFalse(channel.isEmpty)
        assertFalse(channel.isClosedForReceive)
        channel.receive()
        assertFalse(channel.isEmpty)
        assertTrue(channel.isClosedForReceive)
    }

    @Test
    fun testSendClosedWithExceptionReceiveIsEmptyFalse() = runTest {
        val channel = Channel<Int>(1)
        assertTrue(channel.isEmpty)
        assertFalse(channel.isClosedForReceive)
        channel.send(1)
        assertFalse(channel.isEmpty)
        assertFalse(channel.isClosedForReceive)
        channel.close(TestException())
        assertFalse(channel.isEmpty)
        assertFalse(channel.isClosedForReceive)
        channel.receive()
        assertFalse(channel.isEmpty)
        assertTrue(channel.isClosedForReceive)
    }

}
