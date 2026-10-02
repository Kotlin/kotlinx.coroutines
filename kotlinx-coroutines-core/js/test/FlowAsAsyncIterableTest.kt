package kotlinx.coroutines

import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.`return`
import kotlinx.coroutines.internal.`throw`
import kotlinx.coroutines.testing.*
import kotlinx.coroutines.testing.TestException
import kotlin.js.*
import kotlin.test.*

class FlowAsAsyncIterableTest : TestBase() {
    /** Tests that the async iterator obtained from a Flow emits the expected elements. */
    @Test
    fun testFlowToAsyncIteratorBasic() = runTest {
        for (list in listOf(
            listOf(1, 2, 3),
            emptyList(),
            listOf(42)
        )) {
            val flow = list.asFlow()
            val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
            for (el in list) {
                assertNextStepToBe(iterator, value = el, done = false)
            }
            assertNextStepToBe(iterator, done = true)
        }
    }

    /** Tests that the flow only wakes up to emit new elements when the `next` query is issued to the async iterator. */
    @Test
    fun testFlowToAsyncIteratorSynchronousExecution() = runTest {
        val flow = flow {
            expect(2)
            emit(1)
            expect(4)
            emit(2)
            expect(6)
        }
        val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        globalQueueRedispatch()
        expect(1)
        assertNextStepToBe(iterator, value = 1, done = false)
        globalQueueRedispatch()
        expect(3)
        assertNextStepToBe(iterator, value = 2, done = false)
        globalQueueRedispatch()
        expect(5)
        assertNextStepToBe(iterator, done = true)
        finish(7)
    }

    /** Tests the behavior of flow async iterator after all the elements have been emitted. */
    @Test
    fun testFlowToAsyncIteratorCommandsAfterLastElement() = runTest {
        for (shouldAwaitImmediately in listOf(true, false)) {
            for (list in listOf(
                listOf(1, 2, 3),
                emptyList(),
                listOf(100)
            )) {
                suspend fun check(block: suspend (JsAsyncIterator<Int>) -> Unit): Boolean {
                    var continuedAfterLastElement = false
                    val flow = flow {
                        list.forEach { emit(it); yield() }
                        continuedAfterLastElement = true
                    }
                    val iterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
                    val nextRequests = list.map { element ->
                        iterator.next().also {
                            if (shouldAwaitImmediately) { it.assertResolvesWith(done = false, value = element) }
                        }
                    }
                    /** In the iterator, the execution is suspended right after the last element got emitted
                     * but before the iterator recognizes that it's done. */
                    block(iterator)
                    iterator.assertConsistentCompletedState()
                    nextRequests.zip(list).forEach { (promise, expected) ->
                        promise.assertResolvesWith(done = false, value = expected)
                    }
                    return continuedAfterLastElement
                }
                /* We check the behaviors of various final commands to an iterator that isn't finished but has no more
                   elements, and then we check how various operations behave on an iterator completed each way. */
                for (firstCommand in EarlyExitType.entries) {
                    val continuedAfterLastElement = check {
                        it.assertCompletesProperly(firstCommand)
                    }
                    assertFalse(continuedAfterLastElement)
                }
                run { // separate case for a normal exit
                    val continuedAfterLastElement = check {
                        assertNextStepToBe(it, done = true)
                    }
                    assertTrue(continuedAfterLastElement)
                }
            }
        }
    }

    /** Tests the behavior of the async iterator over a flow . */
    @Test
    fun testFlowToAsyncIteratorFailing() = runTest {
        val exception = TestException()
        val failingFlow = flow {
            emit(1)
            throw exception
        }
        /** Only checking the normal exit, because early exits won't even trigger the `throw` line.
         * See [testFlowToAsyncIteratorCommandsAfterLastElement]. */
        val iterator: JsAsyncIterator<Int> = failingFlow.asDynamic()[js("Symbol.asyncIterator")]()
        assertNextStepToBe(iterator, value = 1, done = false)
        assertFailsWith<TestException> { iterator.next().await() }
        iterator.assertConsistentCompletedState()
    }

    /** Tests the behavior of an async iterator over a flow that ignores the early exit request and throws. */
    @Test
    fun testFlowToAsyncIteratorOverridingFailureException() = runTest {
        val exception = TestException()
        val failingFlow = flow {
            try {
                emit(1)
            } finally {
                globalQueueRedispatch()
                throw exception
            }
        }
        for (terminationCommand in EarlyExitType.entries) {
            val iterator: JsAsyncIterator<Int> = failingFlow.asDynamic()[js("Symbol.asyncIterator")]()
            // Start collecting the flow and suspend in the `try` block:
            assertNextStepToBe(iterator, value = 1, done = false)
            /** In the iterator, the execution is suspended right after the last element got emitted
             * but before the iterator recognizes that it's done. */
            val exception = TestException2()
            val terminationCommandResult = when (terminationCommand) {
                EarlyExitType.RETURN_42 -> iterator.`return`(42)
                EarlyExitType.RETURN -> iterator.`return`()
                EarlyExitType.THROW_ERROR -> iterator.`throw`(exception)
                EarlyExitType.THROW -> iterator.`throw`()
            }
            assertFailsWith<TestException>("$terminationCommand") { terminationCommandResult.await() }
            iterator.assertConsistentCompletedState()
        }
    }


    /** Tests that an early return from an async iterator doesn't run the flow if no elements were requested. */
    @Test
    fun testFlowToAsyncIteratorNotRunningOnImmediateExit() = runTest {
        var poisoned = false
        val flowThatShouldNotRun = flow<Int> {
            poisoned = true
        }
        for (terminationCommand in EarlyExitType.entries) {
            val iterator: JsAsyncIterator<Int> = flowThatShouldNotRun.asDynamic()[js("Symbol.asyncIterator")]()
            iterator.assertCompletesProperly(terminationCommand)
            iterator.assertConsistentCompletedState()
            assertFalse(poisoned)
        }
    }

    /** Tests that early returns from an async iterator don't skip over cleaning up the flow. */
    @Test
    fun testFlowToAsyncIteratorFinalizersOnEarlyReturn() = runTest {
        var resourcesAcquired = 0
        val flowWithFinalizer = flow {
            resourcesAcquired++
            try {
                repeat(5) {
                    emit(it)
                }
            } finally {
                globalQueueRedispatch()
                resourcesAcquired--
            }
        }
        for (terminationCommand in EarlyExitType.entries) {
            val iterator: JsAsyncIterator<Int> = flowWithFinalizer.asDynamic()[js("Symbol.asyncIterator")]()
            assertNextStepToBe(iterator, value = 0, done = false)
            assertEquals(1, resourcesAcquired)
            iterator.assertCompletesProperly(terminationCommand)
            assertEquals(0, resourcesAcquired)
            iterator.assertConsistentCompletedState()
        }
    }

    /** Checks how a flow behaves when it receives an early exit command.
     * It is assumed that the iterator is transparent for exceptions. */
    private suspend fun JsAsyncIterator<Int>.assertCompletesProperly(terminationCommand: EarlyExitType) {
        val exception = TestException()
        when (terminationCommand) {
            EarlyExitType.RETURN_42 -> `return`(42).assertResolvesWith(value = 42, done = true)
            EarlyExitType.RETURN -> `return`().assertResolvesWith(done = true)
            EarlyExitType.THROW_ERROR -> assertFailsWith<TestException>{ `throw`(exception).await() }
            EarlyExitType.THROW -> assertFailsWith<Throwable> { `throw`().await() }
        }
    }

    /** Checks how a flow that is already done reacts to future commands.
     * It is assumed that the iterator is transparent for exceptions. */
    private suspend fun JsAsyncIterator<Int>.assertConsistentCompletedState() {
        val exception = TestException2()
        `return`().assertResolvesWith(done = true)
        `return`(42).assertResolvesWith(value = 42, done = true)
        assertFailsWith<TestException2>{ `throw`(exception).await() }
        assertFailsWith<Throwable> { `throw`().await() }
        next().assertResolvesWith(done = true)
    }

    /** Tests that several async iterators obtained from a flow get their own independent copies. */
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

    /** Tests that in a queue of `next` calls to an async iterator obtained from a flow,
     * only the first one will observe a failure. */
    @Test
    fun testFlowToAsyncIteratorQueuedNextOnFailure() = runTest {
        val mayContinue = Job()
        val error = IllegalStateException("Collection failed")
        val iterator: JsAsyncIterator<Int> = flow<Int> {
            mayContinue.join()
            throw error
        }.asDynamic()[js("Symbol.asyncIterator")]()
        val nextRequests = List(3) { iterator.next() }
        mayContinue.complete()
        assertSame(error, assertFailsWith<IllegalStateException> { nextRequests.first().await() })
        // Like in async generators, the requests that were already queued when the collection failed
        // are resolved with `{ value: undefined, done: false }`; only the subsequent ones report completion
        for (pending in nextRequests.subList(1, nextRequests.size)) {
            pending.assertResolvesWith(done = true)
        }
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
        iterator.`return`(null).assertResolvesWith(value = 2, done = false)
        assertTrue(continued)
        assertFalse(emittedSecond)
        assertNextStepToBe(iterator, done = true)
        assertTrue(emittedSecond)
    }

    @Test
    fun testFlowToAsyncIteratorFlowOnCleanup() = runTest {
        val mayCleanup = Job()
        var cleanupDone = false
        val iterator = flow {
            try {
                var i = 0
                while (true) emit(i++)
            } finally {
                withContext(NonCancellable) {
                    mayCleanup.join()
                    cleanupDone = true
                }
            }
        }.flowOn(Dispatchers.Unconfined).asDynamic()[js("Symbol.asyncIterator")]().unsafeCast<JsAsyncIterator<*>>()
        assertNextStepToBe(iterator, value = 0, done = false)
        assertNextStepToBe(iterator, value = 1, done = false)
        // The upstream runs in a separate coroutine (buffered `flowOn`), its cleanup is still awaited
        val returnPromise = iterator.`return`(null)
        assertFalse(cleanupDone)
        mayCleanup.complete()
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
        val iterator: JsAsyncIterator<*> = flow {
            emit(1)
            gate.await()
            upstreamFailed.complete(Unit)
            throw error
        }.flowOn(Dispatchers.Default).onCompletion {
            completed.complete(Unit)
        }.asDynamic()[js("Symbol.asyncIterator")]()
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

    /** Tests that the async iterable obtained from a flow is itself an async iterable,
     * returning itself as the iterator. */
    @Test
    fun testFlowIteratorIsIterable() = runTest {
        val flow = flowOf(10, 20, 30)
        val firstIterator: JsAsyncIterator<Int> = flow.asDynamic()[js("Symbol.asyncIterator")]()
        val asyncIterable = firstIterator.unsafeCast<JsAsyncIterator<*>>()
        val secondIterator = asyncIterable.unsafeCast<JsAsyncIterable<Int>>().asyncIterator()
        assertSame(asyncIterable, secondIterator)
        assertNextStepToBe(firstIterator, value = 10, done = false)
        assertNextStepToBe(secondIterator, value = 20, done = false)
        assertNextStepToBe(firstIterator, value = 30, done = false)
        assertNextStepToBe(secondIterator, done = true)
    }

    private suspend fun <T> assertNextStepToBe(
        iterator: JsAsyncIterator<T>,
        value: T? = js("undefined"),
        done: Boolean = false
    ) {
        iterator.next().assertResolvesWith(done, value)
    }

    private suspend fun <T> Promise<JsIteratorResult<T>>.assertResolvesWith(
        done: Boolean = false,
        value: T? = js("undefined"),
    ) {
        val result = await()
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

/** Redispatch to the global JS queue to make sure there are no pending promises. */
private suspend fun globalQueueRedispatch() = suspendCancellableCoroutine { cont ->
    val _ = Promise.resolve(Unit).then { cont.resumeWith(Result.success(Unit)) }
}
