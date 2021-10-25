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
                TestCoroutineScope(ctx)
            }
        }
    }

    /** Tests that a newly-created [TestCoroutineScope] provides the correct scheduler. */
    @Test
    fun testCreateProvidesScheduler() {
        // Creates a new scheduler.
        run {
            val scope = TestCoroutineScope()
            assertNotNull(scope.coroutineContext[TestCoroutineScheduler])
        }
        // Reuses the scheduler that the dispatcher is linked to.
        run {
            val dispatcher = TestCoroutineDispatcher()
            val scope = TestCoroutineScope(dispatcher)
            assertSame(dispatcher.scheduler, scope.coroutineContext[TestCoroutineScheduler])
        }
        // Uses the scheduler passed to it.
        run {
            val scheduler = TestCoroutineScheduler()
            val scope = TestCoroutineScope(scheduler)
            assertSame(scheduler, scope.coroutineContext[TestCoroutineScheduler])
            assertSame(scheduler, (scope.coroutineContext[ContinuationInterceptor] as TestDispatcher).scheduler)
        }
        // Doesn't touch the passed dispatcher and the scheduler if they match.
        run {
            val scheduler = TestCoroutineScheduler()
            val dispatcher = TestCoroutineDispatcher(scheduler)
            val scope = TestCoroutineScope(scheduler + dispatcher)
            assertSame(scheduler, scope.coroutineContext[TestCoroutineScheduler])
            assertSame(dispatcher, scope.coroutineContext[ContinuationInterceptor])
        }
    }

    /** Tests that the cleanup procedure throws if there were uncompleted delays by the end. */
    @Test
    fun testPresentDelaysThrowing() {
        val scope = TestCoroutineScope()
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
        val scope = TestCoroutineScope()
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
        val scope = TestCoroutineScope()
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
        val scope = TestCoroutineScope()
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
        val scope = TestCoroutineScope(job)
        scope.cleanupTestCoroutines()
        assertFalse(handlerCalled)
    }

    /** Tests that uncaught exceptions are thrown at the cleanup. */
    @Test
    fun testThrowsUncaughtExceptionsOnCleanup() {
        val scope = createTestCoroutineScope()
        val exception = TestException("test")
        scope.launch {
            throw exception
        }
        assertFailsWith<TestException> {
            scope.cleanupTestCoroutines()
        }
    }

    /** Tests that uncaught exceptions take priority over uncompleted jobs when throwing on cleanup. */
    @Test
    fun testUncaughtExceptionsPrioritizedOnCleanup() {
        val scope = createTestCoroutineScope()
        val exception = TestException("test")
        scope.launch {
            throw exception
        }
        scope.launch {
            delay(1000)
        }
        assertFailsWith<TestException> {
            scope.cleanupTestCoroutines()
        }
    }

    /** Tests that cleaning up twice is forbidden. */
    @Test
    fun testClosingTwice() {
        val scope = createTestCoroutineScope()
        scope.cleanupTestCoroutines()
        assertFailsWith<IllegalStateException> {
            scope.cleanupTestCoroutines()
        }
    }

    /** Tests that throwing after cleaning up is forbidden. */
    @Test
    fun testReportingAfterClosing() {
        val scope = createTestCoroutineScope()
        scope.cleanupTestCoroutines()
        assertFailsWith<IllegalStateException> {
            scope.reportException(TestException())
        }
    }

    /** Tests that, when reporting several exceptions, the first one is thrown, with the rest suppressed. */
    @Test
    fun testSuppressedExceptions() {
        createTestCoroutineScope().apply {
            reportException(TestException("x"))
            reportException(TestException("y"))
            reportException(TestException("z"))
            try {
                cleanupTestCoroutines()
                fail("should not be reached")
            } catch (e: TestException) {
                assertEquals("x", e.message)
                assertEquals(2, e.suppressedExceptions.size)
                assertEquals("y", e.suppressedExceptions[0].message)
                assertEquals("z", e.suppressedExceptions[1].message)
            }
        }
    }

    companion object {
        internal val invalidContexts = listOf(
            Dispatchers.Default, // not a [TestDispatcher]
            TestCoroutineDispatcher() + TestCoroutineScheduler(), // the dispatcher is not linked to the scheduler
            CoroutineExceptionHandler { _, _ -> }, // not an `UncaughtExceptionCaptor`
        )
    }
}
