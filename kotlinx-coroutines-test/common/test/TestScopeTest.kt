/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*

class TestScopeTest {
    /** Tests failing to create a [TestCoroutineScope] with incorrect contexts. */
    @Test
    fun testCreateThrowsOnInvalidArguments() {
        for (ctx in invalidContexts) {
            assertFailsWith<IllegalArgumentException> {
                TestScope(ctx)
            }
        }
    }

    /** Tests that a newly-created [TestCoroutineScope] provides the correct scheduler. */
    @Test
    fun testCreateProvidesScheduler() {
        // Creates a new scheduler.
        run {
            val scope = TestScope()
            assertNotNull(scope.coroutineContext[TestCoroutineScheduler])
        }
        // Reuses the scheduler that the dispatcher is linked to.
        run {
            val dispatcher = StandardTestDispatcher()
            val scope = TestScope(dispatcher)
            assertSame(dispatcher.scheduler, scope.coroutineContext[TestCoroutineScheduler])
        }
        // Uses the scheduler passed to it.
        run {
            val scheduler = TestCoroutineScheduler()
            val scope = TestScope(scheduler)
            assertSame(scheduler, scope.coroutineContext[TestCoroutineScheduler])
            assertSame(scheduler, (scope.coroutineContext[ContinuationInterceptor] as TestDispatcher).scheduler)
        }
        // Doesn't touch the passed dispatcher and the scheduler if they match.
        run {
            val scheduler = TestCoroutineScheduler()
            val dispatcher = StandardTestDispatcher(scheduler)
            val scope = TestScope(scheduler + dispatcher)
            assertSame(scheduler, scope.coroutineContext[TestCoroutineScheduler])
            assertSame(dispatcher, scope.coroutineContext[ContinuationInterceptor])
        }
    }

    /** Part of [testCreateProvidesScheduler], disabled for Native */
    @Test
    @NoNative
    fun testCreateReusesScheduler() {
        // Reuses the scheduler of `Dispatchers.Main`
        run {
            val scheduler = TestCoroutineScheduler()
            val mainDispatcher = StandardTestDispatcher(scheduler)
            Dispatchers.setMain(mainDispatcher)
            try {
                val scope = TestScope()
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
                val scope = TestScope(scheduler)
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
        val scope = TestScope()
        var result = false
        scope.launch {
            delay(5)
            result = true
        }
        assertFalse(result)
        scope.asSpecificImplementation().enter()
        assertFailsWith<UncompletedCoroutinesError> { scope.asSpecificImplementation().leave() }
        assertFalse(result)
    }

    /** Tests that the cleanup procedure throws if there were active jobs by the end. */
    @Test
    fun testActiveJobsThrowing() {
        val scope = TestScope()
        var result = false
        val deferred = CompletableDeferred<String>()
        scope.launch {
            deferred.await()
            result = true
        }
        assertFalse(result)
        scope.asSpecificImplementation().enter()
        assertFailsWith<UncompletedCoroutinesError> { scope.asSpecificImplementation().leave() }
        assertFalse(result)
    }

    /** Tests that the cleanup procedure throws even if it detects that the job is already cancelled. */
    @Test
    fun testCancelledDelaysThrowing() {
        val scope = TestScope()
        var result = false
        val deferred = CompletableDeferred<String>()
        val job = scope.launch {
            deferred.await()
            result = true
        }
        job.cancel()
        assertFalse(result)
        scope.asSpecificImplementation().enter()
        assertFailsWith<UncompletedCoroutinesError> { scope.asSpecificImplementation().leave() }
        assertFalse(result)
    }

    /** Tests that uncaught exceptions are thrown at the cleanup. */
    @Test
    fun testGetsCancelledOnChildFailure(): TestResult {
        val scope = TestScope()
        val exception = TestException("test")
        scope.launch {
            throw exception
        }
        return testResultMap({
            try {
                it()
                fail("should not reach")
            } catch (e: TestException) {
                // expected
            }
        }) {
            scope.runTest {
            }
        }
    }

    /** Tests that, when reporting several exceptions, the first one is thrown, with the rest suppressed. */
    @Test
    fun testSuppressedExceptions() {
        TestScope().apply {
            asSpecificImplementation().enter()
            launch(SupervisorJob()) { throw TestException("x") }
            launch(SupervisorJob()) { throw TestException("y") }
            launch(SupervisorJob()) { throw TestException("z") }
            runCurrent()
            val e = asSpecificImplementation().leave()
            assertEquals(3, e.size)
            assertEquals("x", e[0].message)
            assertEquals("y", e[1].message)
            assertEquals("z", e[2].message)
        }
    }

    companion object {
        internal val invalidContexts = listOf(
            Dispatchers.Default, // not a [TestDispatcher]
            CoroutineExceptionHandler { _, _ -> }, // exception handlers can't be overridden
            StandardTestDispatcher() + TestCoroutineScheduler(), // the dispatcher is not linked to the scheduler
        )
    }
}
