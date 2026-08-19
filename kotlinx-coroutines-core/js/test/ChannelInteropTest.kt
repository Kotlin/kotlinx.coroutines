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
        assertNextStepToBe(iterator, value = 1, done = false)
        assertNextStepToBe(iterator, value = 2, done = false)
        assertNextStepToBe(iterator, value = 3, done = false)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testChannelToAsyncIteratorEmpty() = runTest {
        val channel = Channel<Int>().apply { close() }
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testChannelToAsyncIteratorSingle() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()
        launch {
            channel.send(42)
            channel.close()
        }
        assertNextStepToBe(iterator, value = 42, done = false)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testChannelToAsyncIteratorEarlyReturn() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()
        launch {
            channel.send(1)
            assertFailsWith<CancellationException>{
                channel.send(2)
            }.apply {
                assertNull(cause)
            }
        }
        assertNextStepToBe(iterator, value = 1, done = false)
        // Call return() to stop iteration early
        val returnResult = iterator.asDynamic().`return`().unsafeCast<Promise<JsIteratorResult<Int>>>().await()
        assertEquals(true, returnResult.done)
        // Channel should be cancelled
        assertTrue(channel.isClosedForReceive)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testChannelToAsyncIteratorThrow() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()
        val error = js("new Error('test error')")
        launch {
            channel.send(1)
            assertFailsWith<CancellationException> {
                channel.send(2)
            }.apply {
                assertSame(error, cause)
            }
        }
        assertNextStepToBe(iterator, value = 1, done = false)
        // Call throw() to cancel the iterator
        assertFailsWith<Throwable> { iterator.`throw`(error).await() }
            .apply { assertEquals("test error", message) }
        // Channel should not be cancelled
        assertTrue(channel.isClosedForReceive)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testChannelToAsyncIteratorWithBufferedChannel() = runTest {
        val channel = Channel<Int>(capacity = 3)
        channel.send(1)
        channel.send(2)
        channel.send(3)
        channel.close()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, value = 1, done = false)
        assertNextStepToBe(iterator, value = 2, done = false)
        assertNextStepToBe(iterator, value = 3, done = false)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testChannelToAsyncIteratorWithConflatedChannel() = runTest {
        val channel = Channel<Int>(Channel.CONFLATED)
        channel.send(1)
        channel.send(2)
        channel.send(3) // Previous values should be conflated
        channel.close()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, value = 3, done = false)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testChannelToAsyncIteratorWithException() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()
        launch {
            channel.send(1)
            channel.close(IllegalStateException("Test exception"))
        }
        assertNextStepToBe(iterator, value = 1, done = false)
        // Next call should throw the exception
        assertFailsWith<IllegalStateException> { iterator.next().await() }
            .apply { assertEquals("Test exception", message) }
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
        assertNextStepToBe(iterator1, value = 1, done = false)
        assertNextStepToBe(iterator2, value = 2, done = false)
        assertNextStepToBe(iterator1, value = 3, done = false)
        assertNextStepToBe(iterator2, value = 4, done = false)
        assertNextStepToBe(iterator1, done = true)
        assertNextStepToBe(iterator2, done = true)
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
            assertNextStepToBe(iterator, value = i, done = false)
        }
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testChannelToAsyncIteratorThrowNoArgument() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()
        launch {
            channel.send(1)
            assertFailsWith<CancellationException> {
                channel.send(2)
            }.apply {
                assertNull(cause)
            }
        }
        assertNextStepToBe(iterator, value = 1, done = false)
        // Call throw() with no argument to cancel the iterator
        assertFailsWith<Throwable> { iterator.asDynamic().`throw`().unsafeCast<Promise<JsIteratorResult<Int>>>().await() }
            .apply { assertEquals("Promise rejected with a non-Throwable exception", message) }
        // Channel should not be cancelled
        assertTrue(channel.isClosedForReceive)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testChannelToAsyncIteratorEarlyReturnWithValue() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel.asDynamic()[js("Symbol.asyncIterator")]()
        launch {
            channel.send(1)
            assertFailsWith<CancellationException> {
                channel.send(2)
            }.apply {
                assertNull(cause)
            }
        }
        assertNextStepToBe(iterator, value = 1, done = false)
        // Call return(value) to stop iteration early, passing a return value
        val returnResult = iterator.`return`(42).await()
        assertEquals(true, returnResult.done)
        assertEquals(42, returnResult.value)
        // Channel should not be cancelled
        assertTrue(channel.isClosedForReceive)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testChannelToAsyncIteratorNoCancelOnEarlyReturn() = runTest {
        val channel = Channel<Int>(capacity = 1)
        val iterator = channel.asyncIterator(cancelOnEarlyExit = false)
        launch {
            channel.send(1)
            channel.send(2)
            channel.close()
        }
        assertNextStepToBe(iterator, value = 1, done = false)
        val returnResult = iterator.asDynamic().`return`().unsafeCast<Promise<JsIteratorResult<Int>>>().await()
        assertEquals(true, returnResult.done)
        assertFalse(channel.isClosedForReceive)
        assertEquals(2, channel.receive())
        assertTrue(channel.isClosedForReceive)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testAsAsyncIterableOptionsPreventCancelTrue() = runTest {
        val channel = Channel<Int>(capacity = 1)
        val iterator: JsAsyncIterator<Int> = channel
            .asAsyncIterable(ChannelIteratorOptions(preventCancel = true))
            .asDynamic()[js("Symbol.asyncIterator")]()
        launch {
            channel.send(1)
            channel.send(2)
            channel.close()
        }
        assertNextStepToBe(iterator, value = 1, done = false)
        val returnResult = iterator.asDynamic().`return`().unsafeCast<Promise<JsIteratorResult<Int>>>().await()
        assertEquals(true, returnResult.done)
        assertFalse(channel.isClosedForReceive)
        assertEquals(2, channel.receive())
        assertTrue(channel.isClosedForReceive)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testAsAsyncIterableOptionsPreventCancelFalse() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel
            .asAsyncIterable(ChannelIteratorOptions(preventCancel = false))
            .asDynamic()[js("Symbol.asyncIterator")]()
        launch {
            channel.send(1)
            assertFailsWith<CancellationException> {
                channel.send(2)
            }.apply {
                assertNull(cause)
            }
        }
        assertNextStepToBe(iterator, value = 1, done = false)
        val returnResult = iterator.asDynamic().`return`().unsafeCast<Promise<JsIteratorResult<Int>>>().await()
        assertEquals(true, returnResult.done)
        assertTrue(channel.isClosedForReceive)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testValuesOptionsPreventCancelTrue() = runTest {
        val channel = Channel<Int>(capacity = 1)
        val iterator: JsAsyncIterator<Int> = channel
            .asDynamic()
            .values(ChannelIteratorOptions(preventCancel = true))
            .unsafeCast<JsAsyncIterator<Int>>()
        val error = js("new Error('test error')")
        launch {
            channel.send(1)
            channel.send(2)
            channel.close()
        }
        assertNextStepToBe(iterator, value = 1, done = false)
        assertFailsWith<Throwable> { iterator.`throw`(error).await() }
            .apply { assertEquals("test error", message) }
        assertFalse(channel.isClosedForReceive)
        assertEquals(2, channel.receive())
        assertTrue(channel.isClosedForReceive)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testValuesOptionsPreventCancelFalseByDefault() = runTest {
        val channel = Channel<Int>()
        val iterator: JsAsyncIterator<Int> = channel
            .asDynamic()
            .values(ChannelIteratorOptions(preventCancel = null))
            .unsafeCast<JsAsyncIterator<Int>>()
        val error = js("new Error('test error')")
        launch {
            channel.send(1)
            assertFailsWith<CancellationException> {
                channel.send(2)
            }.apply {
                assertSame(error, cause)
            }
        }
        assertNextStepToBe(iterator, value = 1, done = false)
        assertFailsWith<Throwable> { iterator.`throw`(error).await() }
            .apply { assertEquals("test error", message) }
        assertTrue(channel.isClosedForReceive)
        assertNextStepToBe(iterator, done = true)
    }

    private suspend fun <T> assertNextStepToBe(
        iterator: JsAsyncIterator<T>,
        value: T? = js("undefined"),
        done: Boolean = false
    ) {
        val result = iterator.next().await()
        assertEquals(done, result.done)
        assertEquals(value, result.value)
    }
}
