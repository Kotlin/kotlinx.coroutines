package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.testing.*
import kotlin.js.*
import kotlin.test.*

class ChannelInteropTest : TestBase() {

    // ===== Channel to AsyncIterator tests =====

    @Test
    fun testChannelToAsyncIteratorBasic() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        launch {
            channel.send(1)
            channel.send(2)
            channel.send(3)
            channel.close()
        }

        val result1 = iterator.next().await()
        assertEquals(1, result1.value)
        assertEquals(false, result1.done)

        val result2 = iterator.next().await()
        assertEquals(2, result2.value)
        assertEquals(false, result2.done)

        val result3 = iterator.next().await()
        assertEquals(3, result3.value)
        assertEquals(false, result3.done)

        val result4 = iterator.next().await()
        assertEquals(true, result4.done)
    }

    @Test
    fun testChannelToAsyncIteratorEmpty() = runTest {
        val channel = Channel<Int>()
        channel.close()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        val result = iterator.next().await()
        assertEquals(true, result.done)
    }

    @Test
    fun testChannelToAsyncIteratorSingle() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        launch {
            channel.send(42)
            channel.close()
        }

        val result1 = iterator.next().await()
        assertEquals(42, result1.value)
        assertEquals(false, result1.done)

        val result2 = iterator.next().await()
        assertEquals(true, result2.done)
    }

    @Test
    fun testChannelToAsyncIteratorEarlyReturn() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        launch {
            channel.send(1)
            channel.send(2)
            channel.send(3)
            channel.send(4)
            channel.send(5)
        }

        val result1 = iterator.next().await()
        assertEquals(1, result1.value)

        // Call return() to stop iteration early
        val returnResult = iterator.`return`().await()
        assertEquals(true, returnResult.done)

        // Channel should be cancelled
        assertTrue(channel.isClosedForReceive)
    }

    @Test
    fun testChannelToAsyncIteratorThrow() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        launch {
            channel.send(1)
            channel.send(2)
            channel.send(3)
        }

        val result1 = iterator.next().await()
        assertEquals(1, result1.value)

        // Call throw() to cancel the iterator
        val error = js("new Error('test error')")
        try {
            iterator.`throw`(error).await()
            fail("Should have thrown")
        } catch (e: Throwable) {
            // Expected
        }

        // Channel should be cancelled
        assertTrue(channel.isClosedForReceive)
    }

    @Test
    fun testChannelToAsyncIteratorWithBufferedChannel() = runTest {
        val channel = Channel<Int>(capacity = 3)
        channel.send(1)
        channel.send(2)
        channel.send(3)
        channel.close()

        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        val result1 = iterator.next().await()
        assertEquals(1, result1.value)
        assertEquals(false, result1.done)

        val result2 = iterator.next().await()
        assertEquals(2, result2.value)
        assertEquals(false, result2.done)

        val result3 = iterator.next().await()
        assertEquals(3, result3.value)
        assertEquals(false, result3.done)

        val result4 = iterator.next().await()
        assertEquals(true, result4.done)
    }

    @Test
    fun testChannelToAsyncIteratorWithRendezvousChannel() = runTest {
        val channel = Channel<Int>(Channel.RENDEZVOUS)
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        launch {
            channel.send(10)
            channel.send(20)
            channel.close()
        }

        val result1 = iterator.next().await()
        assertEquals(10, result1.value)
        assertEquals(false, result1.done)

        val result2 = iterator.next().await()
        assertEquals(20, result2.value)
        assertEquals(false, result2.done)

        val result3 = iterator.next().await()
        assertEquals(true, result3.done)
    }

    @Test
    fun testChannelToAsyncIteratorWithConflatedChannel() = runTest {
        val channel = Channel<Int>(Channel.CONFLATED)
        channel.send(1)
        channel.send(2)
        channel.send(3) // Previous values should be conflated
        channel.close()

        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        val result1 = iterator.next().await()
        assertEquals(3, result1.value) // Only the last value
        assertEquals(false, result1.done)

        val result2 = iterator.next().await()
        assertEquals(true, result2.done)
    }

    @Test
    fun testChannelToAsyncIteratorWithException() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        launch {
            channel.send(1)
            channel.close(IllegalStateException("Test exception"))
        }

        val result1 = iterator.next().await()
        assertEquals(1, result1.value)

        // Next call should throw the exception
        try {
            iterator.next().await()
            fail("Should have thrown exception")
        } catch (e: IllegalStateException) {
            assertEquals("Test exception", e.message)
        }
    }

    @Test
    fun testChannelToAsyncIteratorMultipleIterators() = runTest {
        val channel = Channel<Int>()
        val iterator1: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()
        val iterator2: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        launch {
            channel.send(1)
            channel.send(2)
            channel.send(3)
            channel.send(4)
            channel.close()
        }

        // Both iterators should be able to consume from the channel
        // (they compete for elements)
        val result1 = iterator1.next().await()
        assertEquals(1, result1.value)

        val result2 = iterator2.next().await()
        assertEquals(2, result2.value)

        val result3 = iterator1.next().await()
        assertEquals(3, result3.value)

        val result4 = iterator2.next().await()
        assertEquals(4, result4.value)

        val result5 = iterator1.next().await()
        assertEquals(true, result5.done)

        val result6 = iterator2.next().await()
        assertEquals(true, result6.done)
    }

    @Test
    fun testChannelToAsyncIteratorWithUnlimitedChannel() = runTest {
        val channel = Channel<Int>(Channel.UNLIMITED)

        // Send many elements
        repeat(100) { channel.send(it) }
        channel.close()

        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()

        // Read all elements
        repeat(100) { i ->
            val result = iterator.next().await()
            assertEquals(i, result.value)
            assertEquals(false, result.done)
        }

        val finalResult = iterator.next().await()
        assertEquals(true, finalResult.done)
    }
}
