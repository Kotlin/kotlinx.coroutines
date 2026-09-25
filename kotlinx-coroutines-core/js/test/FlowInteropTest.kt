@file:OptIn(ExperimentalCoroutinesApi::class)
package kotlinx.coroutines

import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.testing.*
import kotlin.js.*
import kotlin.test.*
import kotlin.time.Duration.Companion.milliseconds

class FlowInteropTest : TestBase() {

    @Test
    fun testFlowToAsyncIteratorBasic() = runTest {
        val flow = flowOf(1, 2, 3)
        val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, value = 1, done = false)
        assertNextStepToBe(iterator, value = 2, done = false)
        assertNextStepToBe(iterator, value = 3, done = false)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorEmpty() = runTest {
        val flow = emptyFlow<Int>()
        val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorSingle() = runTest {
        val flow = flowOf(42)
        val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, value = 42, done = false)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorSynchronousExecution() = runTest {
        var emittedSecond = false
        val flow = flow {
            emit(1)
            emittedSecond = true
            emit(2)
        }
        val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, value = 1, done = false)
        assertFalse(emittedSecond)
        assertNextStepToBe(iterator, value = 2, done = false)
        assertTrue(emittedSecond)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorEarlyReturnWaitsForCleanup() = runTest {
        var cleanupDone = false
        val flow = flow {
            try {
                emit(1)
                emit(2)
            } finally {
                withContext(NonCancellable) {
                    delay(50.milliseconds)
                    cleanupDone = true
                }
            }
        }
        val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, value = 1, done = false)
        val returnPromise = iterator.asDynamic().`return`(42)
            .unsafeCast<Promise<JsIteratorResult<Int>>>()
        assertFalse(cleanupDone)
        val returnResult = returnPromise.await()
        assertTrue(cleanupDone)
        assertEquals(true, returnResult.done)
        assertEquals(42, returnResult.value)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorEarlyThrowWaitsForCleanup() = runTest {
        var cleanupDone = false
        val flow = flow {
            try {
                emit(1)
                emit(2)
            } finally {
                withContext(NonCancellable) {
                    delay(50.milliseconds)
                    cleanupDone = true
                }
            }
        }
        val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, value = 1, done = false)
        val error = js("new Error('test error')")
        val throwPromise = iterator.`throw`(error)
        assertFalse(cleanupDone)
        assertFailsWith<Throwable> { throwPromise.await() }
            .apply { assertEquals("test error", message) }
        assertTrue(cleanupDone)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorReleasesResourceLikeFirst() = runTest {
        var globalResourceTaken = false
        val resourceUsingFlow = flow {
            globalResourceTaken = true
            try {
                emit(1)
            } finally {
                withContext(NonCancellable) {
                    delay(50.milliseconds)
                    globalResourceTaken = false
                }
            }
        }
        assertEquals(1, resourceUsingFlow.first())
        assertFalse(globalResourceTaken)
        // The channel-based approach: the resource is still taken when `receive()` returns
        coroutineScope {
            val channel = resourceUsingFlow.buffer(0).produceIn(this)
            assertEquals(1, channel.receive())
            assertTrue(globalResourceTaken)
            channel.cancel()
        }
        assertFalse(globalResourceTaken)
        val earlyExitIterator = resourceUsingFlow.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        assertNextStepToBe(earlyExitIterator, value = 1, done = false)
        assertTrue(globalResourceTaken)
        assertTrue(earlyExitIterator.`return`(null).await().done)
        assertFalse(globalResourceTaken)
        val fullIterator = resourceUsingFlow.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        assertNextStepToBe(fullIterator, value = 1, done = false)
        assertTrue(globalResourceTaken)
        assertNextStepToBe(fullIterator, done = true)
        assertFalse(globalResourceTaken)
    }


    @Test
    fun testFlowToAsyncIteratorReturnAfterFailure() = runTest {
        val error = IllegalStateException("Collection failed")
        val iterator = flow {
            emit(1)
            throw error
        }.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        assertNextStepToBe(iterator, value = 1, done = false)
        assertSame(error, assertFailsWith<IllegalStateException> { iterator.next().await() })
        // The collection is already finished, so the value passed to `return` is not relayed.
        val result = iterator.`return`(5).await()
        assertTrue(result.done)
        assertEquals(5, result.value)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorCloseBeforeCollection() = runTest {
        for (useThrow in listOf(false, true)) {
            val iterator = flow<Int> {
                fail("Collection should not start")
            }.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
            val error = IllegalStateException("Early exit")
            repeat(2) {
                if (useThrow) {
                    assertSame(error, assertFailsWith<IllegalStateException> { iterator.`throw`(error).await() })
                } else {
                    val result = iterator.`return`(42).await()
                    assertTrue(result.done)
                    assertEquals(42, result.value)
                }
                assertNextStepToBe(iterator, done = true)
            }
        }
    }

    @Test
    fun testFlowToAsyncIteratorCleanupExceptionOnThrow() = runTest {
        val cleanupError = IllegalStateException("Cleanup failed")
        val iterator = flow {
            try {
                emit(1)
            } finally {
                withContext(NonCancellable) {
                    yield()
                    throw cleanupError
                }
            }
        }.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        assertNextStepToBe(iterator, value = 1, done = false)
        val error = IllegalArgumentException("Early exit")
        assertSame(cleanupError, assertFailsWith<IllegalStateException> { iterator.`throw`(error).await() })
        assertSame(error, assertFailsWith<IllegalArgumentException> { iterator.`throw`(error).await() })
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorWithException() = runTest {
        val flow = flow {
            emit(1)
            throw IllegalStateException("Test exception")
        }
        val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, value = 1, done = false)
        assertFailsWith<IllegalStateException> { iterator.next().await() }
            .apply { assertEquals("Test exception", message) }
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorMultipleIterators() = runTest {
        var collectionCount = 0
        val flow = flow {
            val id = ++collectionCount
            emit(id * 10)
            emit(id * 10 + 1)
        }
        val iterator1: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        val iterator2: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator1, value = 10, done = false)
        assertNextStepToBe(iterator2, value = 20, done = false)
        assertNextStepToBe(iterator1, value = 11, done = false)
        assertNextStepToBe(iterator2, value = 21, done = false)
        assertNextStepToBe(iterator1, done = true)
        assertNextStepToBe(iterator2, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorConcurrentNext() = runTest {
        val flow = flowOf(1, 2, 3)
        val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        val p1 = iterator.next()
        val p2 = iterator.next()
        val p3 = iterator.next()
        val r1 = p1.await()
        val r2 = p2.await()
        val r3 = p3.await()
        assertEquals(1, r1.value)
        assertEquals(false, r1.done)
        assertEquals(2, r2.value)
        assertEquals(false, r2.done)
        assertEquals(3, r3.value)
        assertEquals(false, r3.done)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorQueuedNextOnFailure() = runTest {
        val gate = CompletableDeferred<Unit>()
        val error = IllegalStateException("Collection failed")
        val iterator = flow<Int> {
            gate.await()
            throw error
        }.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        val first = iterator.next()
        val second = iterator.next()
        val third = iterator.next()
        gate.complete(Unit)
        assertSame(error, assertFailsWith<IllegalStateException> { first.await() })
        // Like in async generators, the requests that were already queued when the collection failed
        // are resolved with `{ value: undefined, done: false }`; only the subsequent ones report completion
        for (pending in listOf(second, third)) {
            val result = pending.await()
            assertTrue(result.done)
            assertEquals(js("undefined"), result.value)
        }
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorQueuedEarlyExit() = runTest {
        for (useThrow in listOf(false, true)) {
            var cleanupDone = false
            var emittedSecond = false
            val iterator = flow {
                try {
                    delay(50.milliseconds)
                    emit(1)
                    emittedSecond = true
                    emit(2)
                } finally {
                    withContext(NonCancellable) {
                        delay(50.milliseconds)
                        cleanupDone = true
                    }
                }
            }.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
            // Like in async generators, `return`/`throw` are queued after the pending `next()`
            // and are only processed once the flow reaches the next `emit`
            val first = iterator.next()
            val earlyExit = if (useThrow) iterator.`throw`(IllegalStateException("Early exit")) else iterator.`return`(null)
            val firstResult = first.await()
            assertFalse(firstResult.done)
            assertEquals(1, firstResult.value)
            assertFalse(cleanupDone)
            if (useThrow) {
                assertFailsWith<IllegalStateException> { earlyExit.await() }
                    .apply { assertEquals("Early exit", message) }
            } else {
                assertTrue(earlyExit.await().done)
            }
            assertTrue(cleanupDone)
            assertFalse(emittedSecond)
            assertNextStepToBe(iterator, done = true)
        }
    }

    @Test
    fun testFlowToAsyncIteratorSynchronousResume() = runTest {
        var emitted = 0
        val iterator = flow {
            emit(++emitted)
            emit(++emitted)
            emit(++emitted)
        }.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        val first = iterator.next()
        assertEquals(1, emitted)
        assertEquals(1, first.await().value)
        val second = iterator.next()
        assertEquals(2, emitted)
        assertEquals(2, second.await().value)
        assertNextStepToBe(iterator, value = 3, done = false)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorQueuedNextWhileSuspended() = runTest {
        val iterator = flow {
            emit(1)
            delay(50.milliseconds)
            emit(2)
            emit(3)
        }.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        assertNextStepToBe(iterator, value = 1, done = false)
        val second = iterator.next()
        val third = iterator.next()
        assertEquals(2, second.await().value)
        assertEquals(3, third.await().value)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorContinuesAfterCaughtCancellation() = runTest {
        var continued = false
        var emittedSecond = false
        val iterator = flow {
            try {
                emit(1)
            } catch (_: CancellationException) {
                // ignore the cancellation and try to go on
            }
            continued = true
            emit(2)
            emittedSecond = true
        }.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        assertNextStepToBe(iterator, value = 1, done = false)
        // Like an async generator that catches the exception and keeps yielding,
        // the flow that survives the cancellation relays the next element to the `return` request
        val returnResult = iterator.`return`(null).await()
        assertTrue(continued)
        assertFalse(returnResult.done)
        assertEquals(2, returnResult.value)
        assertFalse(emittedSecond)
        assertNextStepToBe(iterator, done = true)
        assertTrue(emittedSecond)
    }

    @Test
    fun testFlowToAsyncIteratorFlowOnCleanup() = runTest {
        var cleanupDone = false
        val iterator = flow {
            try {
                var i = 0
                while (true) emit(i++)
            } finally {
                withContext(NonCancellable) {
                    delay(50.milliseconds)
                    cleanupDone = true
                }
            }
        }.flowOn(Dispatchers.Unconfined).asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        assertNextStepToBe(iterator, value = 0, done = false)
        assertNextStepToBe(iterator, value = 1, done = false)
        // The upstream runs in a separate coroutine (buffered `flowOn`), its cleanup is still awaited
        val returnPromise = iterator.`return`(null)
        assertFalse(cleanupDone)
        assertTrue(returnPromise.await().done)
        assertTrue(cleanupDone)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIteratorFlowOnFailureWithoutPendingRequest() = runTest {
        val gate = CompletableDeferred<Unit>()
        val upstreamFailed = CompletableDeferred<Unit>()
        val completed = CompletableDeferred<Unit>()
        val error = IllegalStateException("Upstream failed")
        val iterator = flow {
            emit(1)
            gate.await()
            upstreamFailed.complete(Unit)
            throw error
        }.flowOn(Dispatchers.Default).onCompletion { completed.complete(Unit) }.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        assertNextStepToBe(iterator, value = 1, done = false)
        // The upstream fails while the iterator is idle (no pending `next()`): the failure must not be lost
        gate.complete(Unit)
        upstreamFailed.await()
        yield()
        // The downstream does not make progress until the next request arrives
        assertFalse(completed.isCompleted)
        assertSame(error, assertFailsWith<IllegalStateException> { iterator.next().await() })
        assertTrue(completed.isCompleted)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    fun testFlowToAsyncIterableProtocol() = runTest {
        val flow = flowOf(10, 20, 30)
        val asyncIterable = flow.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        val iterator = asyncIterable.unsafeCast<JsAsyncIterable<Int>>().asyncIterator()
        assertSame(asyncIterable, iterator)
        assertNextStepToBe(iterator, value = 10, done = false)
        assertNextStepToBe(iterator, value = 20, done = false)
        assertNextStepToBe(iterator, value = 30, done = false)
        assertNextStepToBe(iterator, done = true)
    }

    @Test
    // Reflect the behavior in semantic: https://pl.kotl.in/WrFYnTdL9
    fun testFlowToAsyncIterableProtocolBreak() = runTest {
        var cleanupDone = false
        var emittedThird = false
        val flow = flow {
            try {
                emit(1)
                emit(2)
                emittedThird = true
                emit(3)
            } finally {
                withContext(NonCancellable) {
                    delay(50.milliseconds)
                    cleanupDone = true
                }
            }
        }
        val iterator = flow.asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>().unsafeCast<JsAsyncIterable<Int>>().asyncIterator()
        assertNextStepToBe(iterator, value = 1, done = false)
        assertNextStepToBe(iterator, value = 2, done = false)
        // `break` inside `for await` calls `return()` without arguments and awaits the returned promise
        val returnResult = iterator.`return`()
            .unsafeCast<Promise<JsIteratorResult<Int>>>()
            .await()
        assertTrue(returnResult.done)
        assertEquals(js("undefined"), returnResult.value)
        assertTrue(cleanupDone)
        assertFalse(emittedThird)
        assertNextStepToBe(iterator, done = true)
    }

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
        val iterator = asyncIterator(next = {
            Promise.resolve(if (i < 3) JsIteratorResult(value = i++, done = false) else JsIteratorResult(done = true))
        })
        assertEquals(0, Flow.fromAsyncIterator(iterator).first())
        assertEquals(
            listOf(1, 2),
            Flow.fromAsyncIterator(iterator).toList()
        )
    }

    @Test
    fun testAsyncIteratorToFlowCallsReturnOnEarlyExit() = runTest {
        var i = 0
        var returnCalls = 0
        val iterator = asyncIterator(
            next = { Promise.resolve(JsIteratorResult(value = i++, done = false)) },
            `return` = { returnCalls++; Promise.resolve(JsIteratorResult(value = it, done = true)) }
        )
        assertEquals(
            listOf(0, 1),
            Flow.fromAsyncIterator(iterator).take(2).toList()
        )
        assertEquals(1, returnCalls)
    }

    @Test
    fun testAsyncIteratorToFlowCallsReturnOnCancellationWhileAwaitingNext() = runTest {
        var returnCalls = 0
        val iterator = asyncIterator<Int>(
            next = { Promise { _, _ -> /* never settles */ } },
            `return` = { returnCalls++; Promise.resolve(JsIteratorResult(value = it, done = true)) }
        )
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            Flow.fromAsyncIterator(iterator).collect { expectUnreached() }
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
        val iterator = asyncIterator(
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
            Flow.fromAsyncIterator(iterator).collect { collected.add(it) }
        })
        assertEquals(listOf(1), collected)
        assertEquals(1, returnCalls)
    }

    @Test
    fun testAsyncIteratorToFlowNextThrowsSynchronously() = runTest {
        val error = IllegalStateException("next failed")
        val iterator = asyncIterator<Int>(next = { throw error })
        assertSame(
            error,
            assertFailsWith<IllegalStateException> {
                Flow.fromAsyncIterator(iterator).toList()
            })
    }

    @Test
    fun testAsyncIteratorToFlowDownstreamFailureWithFailingReturn() = runTest {
        var returnCalls = 0
        val downstreamError = IllegalStateException("downstream failed")
        val returnError = IllegalArgumentException("return failed")
        val iterator = asyncIterator(
            next = { Promise.resolve(JsIteratorResult(value = 1, done = false)) },
            `return` = { returnCalls++; Promise.reject(returnError) }
        )
        // The downstream failure must not be replaced by the failure of `return()`
        val e = assertFailsWith<IllegalStateException> {
            Flow.fromAsyncIterator(iterator)
                .collect { throw downstreamError }
        }
        assertSame(downstreamError, e)
        assertEquals(1, returnCalls)
        assertSame(returnError, e.suppressedExceptions.single())
    }

    @Test
    fun testAsyncIteratorToFlowReturnIsAwaited() = runTest {
        var cleanupDone = false
        val iterator = asyncIterator(
            next = { Promise.resolve(JsIteratorResult(value = 1, done = false)) },
            `return` = { value ->
                Promise { resolve, _ ->
                    GlobalScope.launch {
                        delay(50.milliseconds)
                        cleanupDone = true
                        resolve(JsIteratorResult(value = value, done = true))
                    }
                }
            }
        )
        assertEquals(1, Flow.fromAsyncIterator(iterator).first())
        assertTrue(cleanupDone)
    }

    @Test
    fun testAsyncIteratorToFlowNoReturnOnNormalCompletion() = runTest {
        var i = 0
        var returnCalls = 0
        val iterator = asyncIterator(
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
            Flow.fromAsyncIterator(iterator).toList()
        )
        assertEquals(0, returnCalls)
    }

    /** Builds a hand-written async iterator; `return` is omitted from the object when not provided. */
    private fun <T> asyncIterator(
        next: () -> Promise<JsIteratorResult<T>>,
        `return`: ((T?) -> Promise<JsIteratorResult<T>>)? = null
    ): JsAsyncIterator<T> {
        val iterator = js("{}")
        iterator.next = next
        if (`return` != null) iterator.`return` = `return`
        return iterator.unsafeCast<JsAsyncIterator<T>>()
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

    /**
     * Since the methods are not available from Kotlin sources,
     * we're accessing them via fully qualified names in JavaScript
     */
    private fun <T> Flow.Companion.fromAsyncGenerator(x: () -> JsAsyncIterator<T>): Flow<T> =
        asDynamic().fromAsyncGenerator(x)

    private fun <T> Flow.Companion.fromAsyncIterator(x: JsAsyncIterator<T>): Flow<T> =
        asDynamic().fromAsyncIterator(x)
}
