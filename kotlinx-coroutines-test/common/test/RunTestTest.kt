/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlin.test.*
import kotlin.time.*
import kotlin.time.Duration.Companion.milliseconds

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
    fun testRunTestWithZeroDispatchTimeoutWithControlledDispatches() = runTest(dispatchTimeoutMs = 0) {
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

    /** Tests that too low of a dispatch timeout causes crashes. */
    @Test
    fun testRunTestWithSmallDispatchTimeout() = testResultMap({ fn ->
        try {
            fn()
            fail("shouldn't be reached")
        } catch (e: Throwable) {
            assertIs<UncompletedCoroutinesError>(e)
        }
    }) {
        runTest(dispatchTimeoutMs = 100) {
            withContext(Dispatchers.Default) {
                delay(10000)
                3
            }
            fail("shouldn't be reached")
        }
    }

    /**
     * Tests that [runTest] times out after the specified time.
     */
    @Test
    fun testRunTestWithSmallTimeout() = testResultMap({ fn ->
        try {
            fn()
            fail("shouldn't be reached")
        } catch (e: Throwable) {
            assertIs<UncompletedCoroutinesError>(e)
        }
    }) {
        runTest(timeout = 100.milliseconds) {
            withContext(Dispatchers.Default) {
                delay(10000)
                3
            }
            fail("shouldn't be reached")
        }
    }

    /** Tests that [runTest] times out after the specified time, even if the test framework always knows the test is
     * still doing something. */
    @Test
    fun testRunTestWithSmallTimeoutAndManyDispatches() = testResultMap({ fn ->
        try {
            fn()
            fail("shouldn't be reached")
        } catch (e: Throwable) {
            assertIs<UncompletedCoroutinesError>(e)
        }
    }) {
        runTest(timeout = 100.milliseconds) {
            while (true) {
                withContext(Dispatchers.Default) {
                    delay(10)
                    3
                }
            }
        }
    }

    /** Tests that, on timeout, the names of the active coroutines are listed,
     * whereas the names of the completed ones are not. */
    @Test
    @NoJs
    @NoNative
    fun testListingActiveCoroutinesOnTimeout(): TestResult {
        val name1 = "GoodUniqueName"
        val name2 = "BadUniqueName"
        return testResultMap({
            try {
                it()
                fail("unreached")
            } catch (e: UncompletedCoroutinesError) {
                assertContains(e.message ?: "", name1)
                assertFalse((e.message ?: "").contains(name2))
            }
        }) {
            runTest(dispatchTimeoutMs = 10) {
                launch(CoroutineName(name1)) {
                    CompletableDeferred<Unit>().await()
                }
                launch(CoroutineName(name2)) {
                }
            }
        }
    }

    /** Tests that the [UncompletedCoroutinesError] suppresses an exception with which the coroutine is completing. */
    @Test
    fun testFailureWithPendingCoroutine() = testResultMap({
        try {
            it()
            fail("unreached")
        } catch (e: UncompletedCoroutinesError) {
            @Suppress("INVISIBLE_MEMBER")
            val suppressed = unwrap(e).suppressedExceptions
            assertEquals(1, suppressed.size, "$suppressed")
            assertIs<TestException>(suppressed[0]).also {
                assertEquals("A", it.message)
            }
        }
    }) {
        runTest(timeout = 10.milliseconds) {
            launch(start = CoroutineStart.UNDISPATCHED) {
                withContext(NonCancellable + Dispatchers.Default) {
                    delay(100.milliseconds)
                }
            }
            throw TestException("A")
        }
    }

    /** Tests that real delays can be accounted for with a large enough dispatch timeout. */
    @Test
    fun testRunTestWithLargeDispatchTimeout() = runTest(dispatchTimeoutMs = 5000) {
        withContext(Dispatchers.Default) {
            delay(50)
        }
    }

    /** Tests that delays can be accounted for with a large enough timeout. */
    @Test
    fun testRunTestWithLargeTimeout() = runTest(timeout = 5000.milliseconds) {
        withContext(Dispatchers.Default) {
            delay(50)
        }
    }

    /** Tests uncaught exceptions being suppressed by the dispatch timeout error. */
    @Test
    fun testRunTestTimingOutAndThrowing() = testResultMap({ fn ->
        try {
            fn()
            fail("unreached")
        } catch (e: UncompletedCoroutinesError) {
            @Suppress("INVISIBLE_MEMBER")
            val suppressed = unwrap(e).suppressedExceptions
            assertEquals(1, suppressed.size, "$suppressed")
            assertIs<TestException>(suppressed[0]).also {
                assertEquals("A", it.message)
            }
        }
    }) {
        runTest(timeout = 1.milliseconds) {
            coroutineContext[CoroutineExceptionHandler]!!.handleException(coroutineContext, TestException("A"))
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

    /** Tests that [TestScope.runTest] does not inherit the exception handler and works. */
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

    /**
     * Tests that if the main coroutine is completed without a dispatch, [runTest] will not consider this to be
     * inactivity.
     *
     * The test will hang if this is not the case.
     */
    @Test
    fun testCoroutineCompletingWithoutDispatch() = runTest(timeout = Duration.INFINITE) {
        launch(Dispatchers.Default) { delay(100) }
    }
}
