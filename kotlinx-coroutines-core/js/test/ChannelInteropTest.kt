package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.testing.*
import kotlin.js.*
import kotlin.test.*

class ChannelInteropTest : TestBase() {

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
        testAsyncIteratorCancellingOnEarlyReturn { channel ->
            channel.asDynamic()[js("Symbol.asyncIterator")]()
        }
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
    fun testValuesOptionsCancelOnEarlyExitTrue() = runTest {
        testAsyncIteratorCancellingOnEarlyReturn { channel ->
            channel.asyncIterator(cancelOnEarlyExit = true)
        }
        testAsyncIteratorCancellingOnEarlyReturn { channel ->
            channel.asyncIterator()
        }
    }

    @Test
    fun testAsAsyncIterableOptionsCancelOnEarlyExitFalse() = runTest {
        testAsyncIteratorNotCancellingOnEarlyReturn { channel ->
            channel.asyncIterator(cancelOnEarlyExit = false)
        }
    }

    @Test
    fun testAsAsyncIterableOptionsPreventCancelFalse() = runTest {
        testAsyncIteratorCancellingOnEarlyReturn { channel ->
            js("channel.values({ preventCancel: false })[Symbol.asyncIterator]()")
        }
    }

    @Test
    fun testValuesOptionsPreventCancelTrue() = runTest {
        testAsyncIteratorNotCancellingOnEarlyReturn { channel ->
            js("channel.values({ preventCancel: true })[Symbol.asyncIterator]()")
        }
    }

    @Test
    fun testValuesOptionsPreventCancelFalseByDefault() = runTest {
        testAsyncIteratorCancellingOnEarlyReturn { channel ->
            js("channel.values()[Symbol.asyncIterator]()")
        }
    }

    private suspend fun testAsyncIteratorCancellingOnEarlyReturn(
        obtainIterator: (Channel<Int>) -> JsAsyncIterator<Int>
    ) {
        for (earlyExitType in EarlyExitType.entries) {
            coroutineScope {
                val channel = Channel<Int>()
                val iterator: JsAsyncIterator<Int> = obtainIterator(channel)
                val producer = async {
                    channel.send(1)
                    assertFailsWith<CancellationException> {
                        channel.send(2)
                    }
                }
                assertNextStepToBe(iterator, value = 1, done = false)
                when (earlyExitType) {
                    EarlyExitType.RETURN_42 -> {
                        val returnResult = iterator.`return`(42)
                            .unsafeCast<Promise<JsIteratorResult<Int>>>().await()
                        producer.await().apply { assertNull(cause) }
                        assertEquals(true, returnResult.done)
                        assertEquals(42, returnResult.value)
                    }
                    EarlyExitType.RETURN -> {
                        val returnResult = iterator.`return`()
                            .unsafeCast<Promise<JsIteratorResult<Int>>>().await()
                        producer.await().apply { assertNull(cause) }
                        assertEquals(true, returnResult.done)
                    }
                    EarlyExitType.THROW_ERROR -> {
                        val error = js("new Error('test error')")
                        assertFailsWith<Throwable> { iterator.`throw`(error).await() }
                            .apply { assertEquals("test error", message) }
                        producer.await().apply { assertSame(error, cause) }
                    }
                    EarlyExitType.THROW -> {
                        assertFailsWith<Throwable> {
                            iterator.asDynamic().`throw`().unsafeCast<Promise<JsIteratorResult<Int>>>().await()
                        }.apply { assertEquals("Promise rejected with a non-Throwable exception", message) }
                        producer.await().apply { assertNull(cause) }
                    }
                }
                assertTrue(channel.isClosedForReceive)
                assertNextStepToBe(iterator, done = true)
            }
        }
    }

    private suspend fun testAsyncIteratorNotCancellingOnEarlyReturn(
        obtainIterator: (Channel<Int>) -> JsAsyncIterator<Int>
    ) {
        for (earlyExitType in EarlyExitType.entries) {
            coroutineScope {
                val channel = Channel<Int>()
                val iterator: JsAsyncIterator<Int> = obtainIterator(channel)
                launch {
                    channel.send(1)
                    channel.send(2)
                }
                assertNextStepToBe(iterator, value = 1, done = false)
                when (earlyExitType) {
                    EarlyExitType.RETURN_42 -> {
                        val returnResult = iterator.`return`(42)
                            .unsafeCast<Promise<JsIteratorResult<Int>>>().await()
                        assertEquals(true, returnResult.done)
                        assertEquals(42, returnResult.value)
                    }
                    EarlyExitType.RETURN -> {
                        val returnResult = iterator.`return`()
                            .unsafeCast<Promise<JsIteratorResult<Int>>>().await()
                        assertEquals(true, returnResult.done)
                    }
                    EarlyExitType.THROW_ERROR -> {
                        val error = js("new Error('test error')")
                        assertFailsWith<Throwable> { iterator.`throw`(error).await() }
                            .also { assertSame(error, it) }
                    }
                    EarlyExitType.THROW -> {
                        val error = js("new Error('test error')")
                        assertFailsWith<Throwable> {
                            iterator.asDynamic().`throw`().unsafeCast<Promise<JsIteratorResult<Int>>>().await()
                        }.apply { assertEquals("Promise rejected with a non-Throwable exception", message) }
                    }
                }
                assertFalse(channel.isClosedForReceive)
                assertEquals(2, channel.receive())
                assertNextStepToBe(iterator, done = true)
            }
        }
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

    private enum class EarlyExitType {
        RETURN_42,
        RETURN,
        THROW_ERROR,
        THROW,
    }
}
