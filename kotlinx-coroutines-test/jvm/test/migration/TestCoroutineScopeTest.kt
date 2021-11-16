/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("DEPRECATION")

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
        // Reuses the scheduler of `Dispatchers.Main`
        run {
            val scheduler = TestCoroutineScheduler()
            val mainDispatcher = StandardTestDispatcher(scheduler)
            Dispatchers.setMain(mainDispatcher)
            try {
                val scope = createTestCoroutineScope()
                assertSame(scheduler, scope.coroutineContext[TestCoroutineScheduler])
                assertNotSame(mainDispatcher, scope.coroutineContext[ContinuationInterceptor])
            } finally {
                Dispatchers.resetMain()
            }
        }
        // Does not reuse the scheduler of `Dispatchers.Main` if one is explicitly passed
        run {
            val mainDispatcher = StandardTestDispatcher()
            Dispatchers.setMain(mainDispatcher)
            try {
                val scheduler = TestCoroutineScheduler()
                val scope = createTestCoroutineScope(scheduler)
                assertSame(scheduler, scope.coroutineContext[TestCoroutineScheduler])
                assertNotSame(mainDispatcher.scheduler, scope.coroutineContext[TestCoroutineScheduler])
                assertNotSame(mainDispatcher, scope.coroutineContext[ContinuationInterceptor])
            } finally {
                Dispatchers.resetMain()
            }
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

    /** Tests that, when reporting several exceptions, the first one is thrown, with the rest suppressed. */
    @Test
    fun testSuppressedExceptions() {
        createTestCoroutineScope().apply {
            launch(SupervisorJob()) { throw TestException("x") }
            launch(SupervisorJob()) { throw TestException("y") }
            launch(SupervisorJob()) { throw TestException("z") }
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

    /** Tests that constructing a new [TestCoroutineScope] using another one's scope works and overrides the exception
     * handler. */
    @Test
    fun testCopyingContexts() {
        val deferred = CompletableDeferred<Unit>()
        val scope1 = createTestCoroutineScope()
        scope1.launch { deferred.await() } // a pending job in the outer scope
        val scope2 = createTestCoroutineScope(scope1.coroutineContext)
        val scope3 = createTestCoroutineScope(scope1.coroutineContext)
        assertEquals(
            scope1.coroutineContext.minusKey(CoroutineExceptionHandler),
            scope2.coroutineContext.minusKey(CoroutineExceptionHandler))
        scope2.launch(SupervisorJob()) { throw TestException("x") } // will fail the cleanup of scope2
        try {
            scope2.cleanupTestCoroutines()
            fail("should not be reached")
        } catch (e: TestException) { }
        scope3.cleanupTestCoroutines() // the pending job in the outer scope will not cause this to fail
        try {
            scope1.cleanupTestCoroutines()
            fail("should not be reached")
        } catch (e: UncompletedCoroutinesError) {
            // the pending job in the outer scope
        }
    }

    companion object {
        internal val invalidContexts = listOf(
            Dispatchers.Default, // not a [TestDispatcher]
            CoroutineExceptionHandler { _, _ -> }, // not an [UncaughtExceptionCaptor]
            StandardTestDispatcher() + TestCoroutineScheduler(), // the dispatcher is not linked to the scheduler
        )
    }
}