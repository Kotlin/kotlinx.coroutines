package kotlinx.coroutines

import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.JsAsyncIterable
import kotlinx.coroutines.testing.*
import kotlin.js.*
import kotlin.test.*
import kotlinx.coroutines.internal.JsAsyncIterator
import kotlinx.coroutines.internal.JsIteratorResult

class FlowInteropTest : TestBase() {

    // ===== Flow to AsyncIterator tests =====

    @Test
    fun testFlowToAsyncIteratorBasic() = runTest {
        val flow = flowOf(1, 2, 3)
        val iterator: JsAsyncIterator<Int> = flow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()

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
    fun testFlowToAsyncIteratorEmpty() = runTest {
        val flow = emptyFlow<Int>()
        val iterator: JsAsyncIterator<Int> = flow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()

        val result = iterator.next().await()
        assertEquals(true, result.done)
    }

    @Test
    fun testFlowToAsyncIteratorSingle() = runTest {
        val flow = flowOf(42)
        val iterator: JsAsyncIterator<Int> = flow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()

        val result1 = iterator.next().await()
        assertEquals(42, result1.value)
        assertEquals(false, result1.done)

        val result2 = iterator.next().await()
        assertEquals(true, result2.done)
    }

    @Test
    fun testFlowToAsyncIteratorEarlyReturn() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
            emit(4)
            emit(5)
        }
        val iterator: JsAsyncIterator<Int> = flow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()

        val result1 = iterator.next().await()
        assertEquals(1, result1.value)

        // Call return() to stop iteration early
        val returnResult = iterator.`return`().await()
        assertEquals(true, returnResult.done)

        // Next calls should return done
        val result2 = iterator.next().await()
        assertEquals(true, result2.done)
    }

    @Test
    fun testFlowToAsyncIteratorThrow() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
        }
        val iterator: JsAsyncIterator<Int> = flow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()

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
    }

    @Test
    fun testFlowToAsyncIteratorException() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            throw TestException("test exception")
        }
        val iterator: JsAsyncIterator<Int> = flow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()

        val result1 = iterator.next().await()
        assertEquals(1, result1.value)

        val result2 = iterator.next().await()
        assertEquals(2, result2.value)

        // Next call should throw the exception
        try {
            val result = iterator.next().await()
            fail("Should have thrown TestException, but return result ${result.value}")
        } catch (e: TestException) {
            assertEquals("test exception", e.message)
        }
    }

    @Test
    fun testFlowToAsyncIteratorWithTransformations() = runTest {
        val flow = flowOf(1, 2, 3)
            .map { it * 2 }
            .filter { it > 2 }

        val iterator: JsAsyncIterator<Int> = flow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()

        val result1 = iterator.next().await()
        assertEquals(4, result1.value)

        val result2 = iterator.next().await()
        assertEquals(6, result2.value)

        val result3 = iterator.next().await()
        assertEquals(true, result3.done)
    }

    @Test
    fun testFlowToAsyncIteratorCancellationReturnsDone() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
            emit(4)
            emit(5)
        }
        val iterator: JsAsyncIterator<Int> = flow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()

        val result1 = iterator.next().await()
        assertEquals(1, result1.value)
        assertEquals(false, result1.done)

        val result2 = iterator.next().await()
        assertEquals(2, result2.value)
        assertEquals(false, result2.done)

        val returnResult = iterator.`return`().await()
        assertEquals(true, returnResult.done)

        val result3 = iterator.next().await()
        assertEquals(true, result3.done)

        val result4 = iterator.next().await()
        assertEquals(true, result4.done)
    }

    @Test
    fun testFlowToAsyncIteratorCancellationExceptionReturnsDone() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
            throw CancellationException("flow cancelled")
            emit(4) // These should never be emitted
            emit(5)
            emit(6)
        }
        val iterator: JsAsyncIterator<Int> = flow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()

        val result1 = iterator.next().await()
        assertEquals(1, result1.value)
        assertEquals(false, result1.done)

        val result2 = iterator.next().await()
        assertEquals(2, result2.value)
        assertEquals(false, result2.done)

        val result3 = iterator.next().await()
        assertEquals(3, result3.value)
        assertEquals(false, result3.done)

        // When flow throws CancellationException, next() should return done: true
        // without propagating the exception, and unconditionally stop emitting
        val result4 = iterator.next().await()
        assertEquals(true, result4.done)

        // Subsequent calls should also return done: true, ensuring elements after
        // CancellationException are never emitted
        val result5 = iterator.next().await()
        assertEquals(true, result5.done)

        val result6 = iterator.next().await()
        assertEquals(true, result6.done)
    }

    // ===== AsyncIterator to Flow tests =====

    @Test
    fun testAsyncIteratorToFlowBasic() = runTest {
        val asyncIterator = createAsyncIterator(listOf(1, 2, 3))
        val flow = Flow.from(asyncIterator)

        val results = mutableListOf<Int>()
        flow.collect { results.add(it) }

        assertEquals(listOf(1, 2, 3), results)
    }

    @Test
    fun testAsyncIteratorToFlowEmpty() = runTest {
        val asyncIterator = createAsyncIterator(emptyList<Int>())
        val flow = Flow.from(asyncIterator)

        val results = mutableListOf<Int>()
        flow.collect { results.add(it) }

        assertEquals(emptyList(), results)
    }

    @Test
    fun testAsyncIteratorToFlowSingle() = runTest {
        val asyncIterator = createAsyncIterator(listOf(42))
        val flow = Flow.from(asyncIterator)

        val results = mutableListOf<Int>()
        flow.collect { results.add(it) }

        assertEquals(listOf(42), results)
    }

    @Test
    fun testAsyncIteratorToFlowCancellation() = runTest {
        var returnCalled = false
        val asyncIterator = createAsyncIteratorWithCleanup(
            listOf(1, 2, 3, 4, 5),
            onReturn = { returnCalled = true }
        )
        val flow = Flow.from(asyncIterator)

        val results = mutableListOf<Int>()
        flow.take(2).collect { results.add(it) }

        assertEquals(listOf(1, 2), results)
        yield() // Allow cleanup to happen
        assertTrue(returnCalled, "return() should be called on cancellation")
    }

    @Test
    fun testAsyncIteratorToFlowException() = runTest {
        val asyncIterator = createAsyncIteratorWithException(
            listOf(1, 2),
            TestException("iterator error")
        )
        val flow = Flow.from(asyncIterator)

        val results = mutableListOf<Int>()
        try {
            flow.collect { results.add(it) }
            fail("Should have thrown TestException")
        } catch (e: TestException) {
            assertEquals("iterator error", e.message)
        }

        assertEquals(listOf(1, 2), results)
    }

    @Test
    fun testAsyncGeneratorToFlow() = runTest {
        val generator: () -> JsAsyncIterator<Int> = {
            createAsyncIterator(listOf(10, 20, 30))
        }

        val flow = Flow.from(generator)

        val results = mutableListOf<Int>()
        flow.collect { results.add(it) }

        assertEquals(listOf(10, 20, 30), results)
    }

    @Test
    fun testAsyncIterableToFlow() = runTest {
        val asyncIterable = createAsyncIterable(listOf(5, 10, 15))
        val flow = Flow.from(asyncIterable)

        val results = mutableListOf<Int>()
        flow.collect { results.add(it) }

        assertEquals(listOf(5, 10, 15), results)
    }

    @Test
    fun testAsyncIteratorToFlowWithTransformations() = runTest {
        val asyncIterator = createAsyncIterator(listOf(1, 2, 3, 4, 5))
        val flow = Flow.from(asyncIterator)
            .map { it * 2 }
            .filter { it > 5 }

        val results = mutableListOf<Int>()
        flow.collect { results.add(it) }

        assertEquals(listOf(6, 8, 10), results)
    }

    // ===== Round-trip tests =====
    @Test
    fun testRoundTripFlowToAsyncIterableToFlow() = runTest {
        val originalFlow = flowOf(1, 2, 3, 4, 5)
        val convertedFlow = Flow.from(originalFlow.asAsyncIterable())

        val results = mutableListOf<Int>()
        convertedFlow.collect { results.add(it) }

        assertEquals(listOf(1, 2, 3, 4, 5), results)
    }

    @Test
    fun testRoundTripFlowToAsyncIteratorToFlow() = runTest {
        val originalFlow = flowOf(1, 2, 3, 4, 5)
        val iterator: JsAsyncIterator<Int> = originalFlow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()
        val convertedFlow = Flow.from(iterator)

        val results = mutableListOf<Int>()
        convertedFlow.collect { results.add(it) }

        assertEquals(listOf(1, 2, 3, 4, 5), results)
    }

    @Test
    fun testRoundTripAsyncIteratorToFlowToAsyncIterator() = runTest {
        val originalIterator = createAsyncIterator(listOf(10, 20, 30))
        val flow = Flow.from(originalIterator)
        val convertedIterator: JsAsyncIterator<Int> = flow.asAsyncIterable().asDynamic()[js("Symbol.asyncIterator")]()

        val result1 = convertedIterator.next().await()
        assertEquals(10, result1.value)

        val result2 = convertedIterator.next().await()
        assertEquals(20, result2.value)

        val result3 = convertedIterator.next().await()
        assertEquals(30, result3.value)

        val result4 = convertedIterator.next().await()
        assertEquals(true, result4.done)
    }

    // ===== Helper functions =====

    private fun createAsyncIterator(values: List<Int>): JsAsyncIterator<Int> {
        var index = 0
        val iterator = js("({})")
        iterator.next = fun(): Promise<JsIteratorResult<Int>> {
            return if (index < values.size) {
                val value = values[index++]
                Promise.resolve(js("({ value: value, done: false })"))
            } else {
                Promise.resolve(js("({ value: undefined, done: true })"))
            }
        }

        iterator.`return` = fun(): Promise<JsIteratorResult<Int>> {
            return Promise.resolve(js("({ value: undefined, done: true })"))
        }
        iterator.`throw` = fun(error: Throwable): Promise<JsIteratorResult<Int>> {
            return Promise.reject(error)
        }
        return iterator
    }

    private fun createAsyncIteratorWithCleanup(values: List<Int>, onReturn: () -> Unit): JsAsyncIterator<Int> {
        var index = 0
        val iterator = js("({})")
        iterator.next = fun(): Promise<JsIteratorResult<Int>> {
            return if (index < values.size) {
                val value = values[index++]
                Promise.resolve(js("({ value: value, done: false })"))
            } else {
                Promise.resolve(js("({ value: undefined, done: true })"))
            }
        }

        iterator.`return` = fun(): Promise<JsIteratorResult<Int>> {
            onReturn()
            return Promise.resolve(js("({ value: undefined, done: true })"))
        }
        iterator.`throw` = fun(error: Throwable): Promise<JsIteratorResult<Int>> {
            return Promise.reject(error)
        }
        return iterator
    }

    private fun createAsyncIteratorWithException(values: List<Int>, exception: Throwable): JsAsyncIterator<Int> {
        var index = 0
        val iterator = js("({})")
        iterator.next = fun(): Promise<JsIteratorResult<Int>> {
            return if (index < values.size) {
                val value = values[index++]
                Promise.resolve(js("({ value: value, done: false })"))
            } else {
                Promise.reject(exception)
            }
        }

        iterator.`return` = fun(): Promise<JsIteratorResult<Int>> {
            return Promise.resolve(js("({ value: undefined, done: true })"))
        }
        iterator.`throw` = fun(error: Throwable): Promise<JsIteratorResult<Int>> {
            return Promise.reject(error)
        }
        return iterator
    }

    private fun createAsyncIteratorWithCallCounter(values: List<Int>, onNextCall: () -> Unit): JsAsyncIterator<Int> {
        var index = 0
        val iterator = js("({})")
        iterator.next = fun(): Promise<JsIteratorResult<Int>> {
            onNextCall()
            return if (index < values.size) {
                val value = values[index++]
                Promise.resolve(js("({ value: value, done: false })"))
            } else {
                Promise.resolve(js("({ value: undefined, done: true })"))
            }
        }

        iterator.`return` = fun(): Promise<JsIteratorResult<Int>> {
            return Promise.resolve(js("({ value: undefined, done: true })"))
        }
        iterator.`throw` = fun(error: Throwable): Promise<JsIteratorResult<Int>> {
            return Promise.reject(error)
        }
        return iterator
    }

    private fun createAsyncIterable(values: List<Int>): JsAsyncIterable<Int> {
        val iterable = js("({})")
        iterable[js("Symbol.asyncIterator")] = {
            createAsyncIterator(values)
        }
        return iterable
    }
}
