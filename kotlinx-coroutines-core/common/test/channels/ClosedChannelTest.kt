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

    @Test
    fun testClosedToListOk() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            channel.close()
            channel.toList()
        }
    }

    @Test
    fun testClosedWithExceptionToListThrows() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            channel.close(TestException())
            assertFailsWith<TestException> { channel.toList() }
        }
    }

    @Test
    fun testClosedConsumeEachOk() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            channel.close()
            channel.consumeEach {  }
        }
    }

    @Test
    fun testClosedWithExceptionConsumeEachThrows() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            channel.close(TestException())
            assertFailsWith<TestException> { channel.consumeEach {  } }
        }
    }

    /**
     * toList() alternative when a channel might close with an exception.
     */

    @Test
    fun testToListCatching() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Unit>()
            channel.close(TestException())
            val lst = mutableListOf<Unit>()
            while (true) {
                channel.receiveCatching().onClosed { // suspends
                    assertTrue(it is TestException)
                    break
                }.getOrThrow().apply(lst::add)
            }
            assertTrue(lst.isEmpty())
        }
    }

    @Test
    fun testTryToListCatching() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Unit>()
            channel.close(TestException())
            val lst = mutableListOf<Unit>()
            while (true) {
                channel.tryReceive().onClosed { // does not suspend
                    assertTrue(it is TestException)
                    break
                }.onFailure {
                    // empty, but not yet closed
                    break
                }.getOrThrow().apply(lst::add)
            }
            assertTrue(lst.isEmpty())
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
    fun testIsEmpty() = runTest {
        val channel = Channel<Int>()
        assertTrue(channel.isEmpty)
        assertFalse(channel.isClosedForReceive)
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
