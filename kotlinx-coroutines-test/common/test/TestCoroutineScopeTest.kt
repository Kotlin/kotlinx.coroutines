/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*

class TestCoroutineScopeTest {
    /** Tests failing to create a [TestCoroutineScope] with incorrect contexts. */
    @Test
    fun testCreateThrowsOnInvalidArguments() {
        for (ctx in invalidContexts) {
            assertFailsWith<IllegalArgumentException> {
                createTestCoroutineScope(ctx)
            }
        }
    }

    /** Tests that a newly-created [TestCoroutineScope] provides the correct scheduler. */
    @Test
    fun testCreateProvidesScheduler() {
        // Creates a new scheduler.
        run {
            val scope = createTestCoroutineScope()
            assertNotNull(scope.coroutineContext[TestCoroutineScheduler])
        }
        // Reuses the scheduler that the dispatcher is linked to.
        run {
            val dispatcher = StandardTestDispatcher()
            val scope = createTestCoroutineScope(dispatcher)
            assertSame(dispatcher.scheduler, scope.coroutineContext[TestCoroutineScheduler])
        }
        // Uses the scheduler passed to it.
        run {
            val scheduler = TestCoroutineScheduler()
            val scope = createTestCoroutineScope(scheduler)
            assertSame(scheduler, scope.coroutineContext[TestCoroutineScheduler])
            assertSame(scheduler, (scope.coroutineContext[ContinuationInterceptor] as TestDispatcher).scheduler)
        }
        // Doesn't touch the passed dispatcher and the scheduler if they match.
        run {
            val scheduler = TestCoroutineScheduler()
            val dispatcher = StandardTestDispatcher(scheduler)
            val scope = createTestCoroutineScope(scheduler + dispatcher)
            assertSame(scheduler, scope.coroutineContext[TestCoroutineScheduler])
            assertSame(dispatcher, scope.coroutineContext[ContinuationInterceptor])
        }
    }

    /** Tests that the cleanup procedure throws if there were uncompleted delays by the end. */
    @Test
    fun testPresentDelaysThrowing() {
        val scope = createTestCoroutineScope()
        var result = false
        scope.launch {
            delay(5)
            result = true
        }
        assertFalse(result)
        assertFailsWith<AssertionError> { scope.cleanupTestCoroutines() }
        assertFalse(result)
    }

    /** Tests that the cleanup procedure throws if there were active jobs by the end. */
    @Test
    fun testActiveJobsThrowing() {
        val scope = createTestCoroutineScope()
        var result = false
        val deferred = CompletableDeferred<String>()
        scope.launch {
            deferred.await()
            result = true
        }
        assertFalse(result)
        assertFailsWith<AssertionError> { scope.cleanupTestCoroutines() }
        assertFalse(result)
    }

    /** Tests that the cleanup procedure doesn't throw if it detects that the job is already cancelled. */
    @Test
    fun testCancelledDelaysNotThrowing() {
        val scope = createTestCoroutineScope()
        var result = false
        val deferred = CompletableDeferred<String>()
        val job = scope.launch {
            deferred.await()
            result = true
        }
        job.cancel()
        assertFalse(result)
        scope.cleanupTestCoroutines()
        assertFalse(result)
    }

    /** Tests that the coroutine scope completes its job if the job was not passed to it as an argument. */
    @Test
    fun testCompletesOwnJob() {
        val scope = createTestCoroutineScope()
        var handlerCalled = false
        scope.coroutineContext.job.invokeOnCompletion {
            handlerCalled = true
        }
        scope.cleanupTestCoroutines()
        assertTrue(handlerCalled)
    }

    /** Tests that the coroutine scope completes its job if the job was not passed to it as an argument. */
    @Test
    fun testDoesNotCompleteGivenJob() {
        var handlerCalled = false
        val job = Job()
        job.invokeOnCompletion {
            handlerCalled = true
        }
        val scope = createTestCoroutineScope(job)
        scope.cleanupTestCoroutines()
        assertFalse(handlerCalled)
    }

    companion object {
        internal val invalidContexts = listOf(
            Dispatchers.Default, // not a [TestDispatcher]
            StandardTestDispatcher() + TestCoroutineScheduler(), // the dispatcher is not linked to the scheduler
        )
    }
}
