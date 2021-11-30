/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlin.test.*

class RunTestTest {

    /** Tests that [withContext] that sends work to other threads works in [runTest]. */
    @Test
    fun testWithContextDispatching() = runTest {
        var counter = 0
        withContext(Dispatchers.Default) {
            counter += 1
        }
        assertEquals(counter, 1)
    }

    /** Tests that joining [GlobalScope.launch] works in [runTest]. */
    @Test
    fun testJoiningForkedJob() = runTest {
        var counter = 0
        val job = GlobalScope.launch {
            counter += 1
        }
        job.join()
        assertEquals(counter, 1)
    }

    /** Tests [suspendCoroutine] not failing [runTest]. */
    @Test
    fun testSuspendCoroutine() = runTest {
        val answer = suspendCoroutine<Int> {
            it.resume(42)
        }
        assertEquals(42, answer)
    }

    /** Tests that [runTest] attempts to detect it being run inside another [runTest] and failing in such scenarios. */
    @Test
    fun testNestedRunTestForbidden() = runTest {
        assertFailsWith<IllegalStateException> {
            runTest { }
        }
    }

    /** Tests that even the dispatch timeout of `0` is fine if all the dispatches go through the same scheduler. */
    @Test
    fun testRunTestWithZeroTimeoutWithControlledDispatches() = runTest(dispatchTimeoutMs = 0) {
        // below is some arbitrary concurrent code where all dispatches go through the same scheduler.
        launch {
            delay(2000)
        }
        val deferred = async {
            val job = launch(StandardTestDispatcher(testScheduler)) {
                launch {
                    delay(500)
                }
                delay(1000)
            }
            job.join()
        }
        deferred.await()
    }

    /** Tests that a dispatch timeout of `0` will fail the test if there are some dispatches outside the scheduler. */
    @Test
    fun testRunTestWithZeroTimeoutWithUncontrolledDispatches() = testResultMap({ fn ->
        assertFailsWith<UncompletedCoroutinesError> { fn() }
    }) {
        runTest(dispatchTimeoutMs = 0) {
            withContext(Dispatchers.Default) {
                delay(10)
                3
            }
            fail("shouldn't be reached")
        }
    }

    /** Tests that too low of a dispatch timeout causes crashes. */
    @Test
    @NoNative // TODO: timeout leads to `Cannot execute task because event loop was shut down` on Native
    fun testRunTestWithSmallTimeout() = testResultMap({ fn ->
        assertFailsWith<UncompletedCoroutinesError> { fn() }
    }) {
        runTest(dispatchTimeoutMs = 100) {
            withContext(Dispatchers.Default) {
                delay(10000)
                3
            }
            fail("shouldn't be reached")
        }
    }

    /** Tests that real delays can be accounted for with a large enough dispatch timeout. */
    @Test
    fun testRunTestWithLargeTimeout() = runTest(dispatchTimeoutMs = 5000) {
        withContext(Dispatchers.Default) {
            delay(50)
        }
    }

    /** Tests uncaught exceptions taking priority over dispatch timeout in error reports. */
    @Test
    @NoNative // TODO: timeout leads to `Cannot execute task because event loop was shut down` on Native
    fun testRunTestTimingOutAndThrowing() = testResultMap({ fn ->
        assertFailsWith<IllegalArgumentException> { fn() }
    }) {
        runTest(dispatchTimeoutMs = 1) {
            coroutineContext[CoroutineExceptionHandler]!!.handleException(coroutineContext, IllegalArgumentException())
            withContext(Dispatchers.Default) {
                delay(10000)
                3
            }
            fail("shouldn't be reached")
        }
    }

    /** Tests that passing invalid contexts to [runTest] causes it to fail (on JS, without forking). */
    @Test
    fun testRunTestWithIllegalContext() {
        for (ctx in TestScopeTest.invalidContexts) {
            assertFailsWith<IllegalArgumentException> {
                runTest(ctx) { }
            }
        }
    }

    /** Tests that throwing exceptions in [runTest] fails the test with them. */
    @Test
    fun testThrowingInRunTestBody() = testResultMap({
        assertFailsWith<RuntimeException> { it() }
    }) {
        runTest {
            throw RuntimeException()
        }
    }

    /** Tests that throwing exceptions in pending tasks [runTest] fails the test with them. */
    @Test
    fun testThrowingInRunTestPendingTask() = testResultMap({
        assertFailsWith<RuntimeException> { it() }
    }) {
        runTest {
            launch {
                delay(SLOW)
                throw RuntimeException()
            }
        }
    }

    @Test
    fun reproducer2405() = runTest {
        val dispatcher = StandardTestDispatcher(testScheduler)
        var collectedError = false
        withContext(dispatcher) {
            flow { emit(1) }
                .combine(
                    flow<String> { throw IllegalArgumentException() }
                ) { int, string -> int.toString() + string }
                .catch { emit("error") }
                .collect {
                    assertEquals("error", it)
                    collectedError = true
                }
        }
        assertTrue(collectedError)
    }

    /** Tests that, once the test body has thrown, the child coroutines are cancelled. */
    @Test
    fun testChildrenCancellationOnTestBodyFailure(): TestResult {
        var job: Job? = null
        return testResultMap({
            assertFailsWith<AssertionError> { it() }
            assertTrue(job!!.isCancelled)
        }) {
            runTest {
                job = launch {
                    while (true) {
                        delay(1000)
                    }
                }
                throw AssertionError()
            }
        }
    }

    /** Tests that [runTest] reports [TimeoutCancellationException]. */
    @Test
    fun testTimeout() = testResultMap({
        assertFailsWith<TimeoutCancellationException> { it() }
    }) {
        runTest {
            withTimeout(50) {
                launch {
                    delay(1000)
                }
            }
        }
    }

    /** Checks that [runTest] throws the root cause and not [JobCancellationException] when a child coroutine throws. */
    @Test
    fun testRunTestThrowsRootCause() = testResultMap({
        assertFailsWith<TestException> { it() }
    }) {
        runTest {
            launch {
                throw TestException()
            }
        }
    }

    /** Tests that [runTest] completes its job. */
    @Test
    fun testCompletesOwnJob(): TestResult {
        var handlerCalled = false
        return testResultMap({
            it()
            assertTrue(handlerCalled)
        }) {
            runTest {
                coroutineContext.job.invokeOnCompletion {
                    handlerCalled = true
                }
            }
        }
    }

    /** Tests that [runTest] doesn't complete the job that was passed to it as an argument. */
    @Test
    fun testDoesNotCompleteGivenJob(): TestResult {
        var handlerCalled = false
        val job = Job()
        job.invokeOnCompletion {
            handlerCalled = true
        }
        return testResultMap({
            it()
            assertFalse(handlerCalled)
            assertEquals(0, job.children.filter { it.isActive }.count())
        }) {
            runTest(job) {
                assertTrue(coroutineContext.job in job.children)
            }
        }
    }

    /** Tests that, when the test body fails, the reported exceptions are suppressed. */
    @Test
    fun testSuppressedExceptions() = testResultMap({
        try {
            it()
            fail("should not be reached")
        } catch (e: TestException) {
            assertEquals("w", e.message)
            val suppressed = e.suppressedExceptions +
                (e.suppressedExceptions.firstOrNull()?.suppressedExceptions ?: emptyList())
            assertEquals(3, suppressed.size)
            assertEquals("x", suppressed[0].message)
            assertEquals("y", suppressed[1].message)
            assertEquals("z", suppressed[2].message)
        }
    }) {
        runTest {
            launch(SupervisorJob()) { throw TestException("x") }
            launch(SupervisorJob()) { throw TestException("y") }
            launch(SupervisorJob()) { throw TestException("z") }
            throw TestException("w")
        }
    }

    /** Tests that [TestCoroutineScope.runTest] does not inherit the exception handler and works. */
    @Test
    fun testScopeRunTestExceptionHandler(): TestResult {
        val scope = TestScope()
        return testResultMap({
            try {
                it()
                fail("should not be reached")
            } catch (e: TestException) {
                // expected
            }
        }) {
            scope.runTest {
                launch(SupervisorJob()) { throw TestException("x") }
            }
        }
    }
}
