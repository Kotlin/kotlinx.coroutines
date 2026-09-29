package kotlinx.coroutines

import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.testing.*
import kotlin.js.*
import kotlin.test.*

class FlowFromAsyncIterableTest : TestBase() {
    @Test
    fun testAsyncGeneratorToFlowBasic() = runTest {
        // `new Function` is used since the Kotlin/JS compiler does not support `async function*` inside `js()`
        val generator = js("new Function('return async function*() { yield 1; yield 2; yield 3; }')()")
            .unsafeCast<() -> JsAsyncIterator<Int>>()
        assertEquals(
            listOf(1, 2, 3),
            Flow.fromAsyncGenerator(generator).toList()
        )
        assertEquals(
            listOf(1, 2, 3),
            Flow.fromAsyncGenerator(generator).toList()
        )
    }

    @Test
    fun testAsyncIteratorToFlowWithoutReturnMethod() = runTest {
        var i = 0
        val iterable = asyncIterable(next = {
            Promise.resolve(if (i < 3) JsIteratorResult(value = i++, done = false) else JsIteratorResult(done = true))
        })
        assertEquals(0, Flow.fromAsyncIterable(iterable).first())
        assertEquals(
            listOf(1, 2),
            Flow.fromAsyncIterable(iterable).toList()
        )
    }

    @Test
    fun testAsyncIteratorToFlowCallsReturnOnEarlyExit() = runTest {
        var i = 0
        var returnCalls = 0
        val iterable = asyncIterable(
            next = { Promise.resolve(JsIteratorResult(value = i++, done = false)) },
            `return` = { returnCalls++; Promise.resolve(JsIteratorResult(value = it, done = true)) }
        )
        assertEquals(
            listOf(0, 1),
            Flow.fromAsyncIterable(iterable).take(2).toList()
        )
        assertEquals(1, returnCalls)
    }

    @Test
    fun testAsyncIteratorToFlowCallsReturnOnCancellationWhileAwaitingNext() = runTest {
        var returnCalls = 0
        val iterable = asyncIterable<Int>(
            next = { Promise { _, _ -> /* never settles */ } },
            `return` = { returnCalls++; Promise.resolve(JsIteratorResult(value = it, done = true)) }
        )
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            Flow.fromAsyncIterable(iterable).collect { expectUnreached() }
        }
        assertEquals(0, returnCalls)
        job.cancelAndJoin()
        assertEquals(1, returnCalls)
    }

    @Test
    fun testAsyncIteratorToFlowNextRejection() = runTest {
        var i = 0
        var returnCalls = 0
        val error = IllegalStateException("next failed")
        val iterable = asyncIterable(
            next = {
                if (i++ == 0) Promise.resolve(
                    JsIteratorResult(
                        value = 1,
                        done = false
                    )
                ) else Promise.reject(error)
            },
            `return` = { returnCalls++; Promise.reject(IllegalArgumentException("return failed")) }
        )
        val collected = mutableListOf<Int>()
        assertSame(error, assertFailsWith<IllegalStateException> {
            Flow.fromAsyncIterable(iterable).collect { collected.add(it) }
        })
        assertEquals(listOf(1), collected)
        assertEquals(1, returnCalls)
    }

    @Test
    fun testAsyncIteratorToFlowNextThrowsSynchronously() = runTest {
        val error = IllegalStateException("next failed")
        val iterable = asyncIterable<Int>(next = { throw error })
        assertSame(
            error,
            assertFailsWith<IllegalStateException> {
                Flow.fromAsyncIterable(iterable).toList()
            })
    }

    @Test
    fun testAsyncIteratorToFlowDownstreamFailureWithFailingReturn() = runTest {
        var returnCalls = 0
        val downstreamError = IllegalStateException("downstream failed")
        val returnError = IllegalArgumentException("return failed")
        val iterable = asyncIterable(
            next = { Promise.resolve(JsIteratorResult(value = 1, done = false)) },
            `return` = { returnCalls++; Promise.reject(returnError) }
        )
        // The downstream failure must not be replaced by the failure of `return()`
        val e = assertFailsWith<IllegalStateException> {
            Flow.fromAsyncIterable(iterable)
                .collect { throw downstreamError }
        }
        assertSame(downstreamError, e)
        assertEquals(1, returnCalls)
        assertSame(returnError, e.suppressedExceptions.single())
    }

    @Test
    fun testAsyncIteratorToFlowReturnIsAwaited() = runTest {
        var cleanupDone = false
        val iterable = asyncIterable(
            next = { Promise.resolve(JsIteratorResult(value = 1, done = false)) },
            `return` = { value ->
                Promise { resolve, _ ->
                    GlobalScope.launch {
                        yield()
                        cleanupDone = true
                        resolve(JsIteratorResult(value = value, done = true))
                    }
                }
            }
        )
        assertEquals(1, Flow.fromAsyncIterable(iterable).first())
        assertTrue(cleanupDone)
    }

    @Test
    fun testAsyncIteratorToFlowNoReturnOnNormalCompletion() = runTest {
        var i = 0
        var returnCalls = 0
        val iterable = asyncIterable(
            next = {
                Promise.resolve(
                    if (i < 2) JsIteratorResult(
                        value = i++,
                        done = false
                    ) else JsIteratorResult(done = true)
                )
            },
            `return` = { returnCalls++; Promise.resolve(JsIteratorResult(done = true)) }
        )
        assertEquals(
            listOf(0, 1),
            Flow.fromAsyncIterable(iterable).toList()
        )
        assertEquals(0, returnCalls)
    }

    /** Builds a custom async iterable; `return` is omitted from the object when not provided. */
    private fun <T> asyncIterable(
        next: () -> Promise<JsIteratorResult<T>>,
        `return`: ((T?) -> Promise<JsIteratorResult<T>>)? = null
    ): JsAsyncIterable<T> {
        val iterable = js("{}")
        iterable[js("Symbol.asyncIterator")] = {
            val iterator = js("{}")
            iterator.next = next
            if (`return` != null) iterator.`return` = `return`
            iterator.`throw` = { fail("Should not be called") }
            iterator
        }
        return iterable.unsafeCast<JsAsyncIterable<T>>()
    }

    /**
     * Since the methods are not available from Kotlin sources,
     * we're accessing them via fully qualified names in JavaScript
     */
    private fun <T> Flow.Companion.fromAsyncGenerator(x: () -> JsAsyncIterator<T>): Flow<T> =
        asDynamic().fromAsync(x)

    private fun <T> Flow.Companion.fromAsyncIterable(x: JsAsyncIterable<T>): Flow<T> =
        asDynamic().fromAsync(x)
}
