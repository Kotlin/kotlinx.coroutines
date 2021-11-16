/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlin.test.*

/** Copy of [RunTestTest], but for [TestCoroutineScope] */
@Suppress("DEPRECATION")
class RunTestLegacyScopeTest {

    @Test
    fun testWithContextDispatching() = runTestWithLegacyScope {
        var counter = 0
        withContext(Dispatchers.Default) {
            counter += 1
        }
        assertEquals(counter, 1)
    }

    @Test
    fun testJoiningForkedJob() = runTestWithLegacyScope {
        var counter = 0
        val job = GlobalScope.launch {
            counter += 1
        }
        job.join()
        assertEquals(counter, 1)
    }

    @Test
    fun testSuspendCoroutine() = runTestWithLegacyScope {
        val answer = suspendCoroutine<Int> {
            it.resume(42)
        }
        assertEquals(42, answer)
    }

    @Test
    fun testNestedRunTestForbidden() = runTestWithLegacyScope {
        assertFailsWith<IllegalStateException> {
            runTest { }
        }
    }

    @Test
    fun testRunTestWithZeroTimeoutWithControlledDispatches() = runTestWithLegacyScope(dispatchTimeoutMs = 0) {
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

    @Test
    fun testRunTestWithZeroTimeoutWithUncontrolledDispatches() = testResultMap({ fn ->
        assertFailsWith<UncompletedCoroutinesError> { fn() }
    }) {
        runTestWithLegacyScope(dispatchTimeoutMs = 0) {
            withContext(Dispatchers.Default) {
                delay(10)
                3
            }
            fail("shouldn't be reached")
        }
    }

    @Test
    fun testRunTestWithSmallTimeout() = testResultMap({ fn ->
        assertFailsWith<UncompletedCoroutinesError> { fn() }
    }) {
        runTestWithLegacyScope(dispatchTimeoutMs = 100) {
            withContext(Dispatchers.Default) {
                delay(10000)
                3
            }
            fail("shouldn't be reached")
        }
    }

    @Test
    fun testRunTestWithLargeTimeout() = runTestWithLegacyScope(dispatchTimeoutMs = 5000) {
        withContext(Dispatchers.Default) {
            delay(50)
        }
    }

    @Test
    fun testRunTestTimingOutAndThrowing() = testResultMap({ fn ->
        assertFailsWith<IllegalArgumentException> { fn() }
    }) {
        runTestWithLegacyScope(dispatchTimeoutMs = 1) {
            coroutineContext[CoroutineExceptionHandler]!!.handleException(coroutineContext, IllegalArgumentException())
            withContext(Dispatchers.Default) {
                delay(10000)
                3
            }
            fail("shouldn't be reached")
        }
    }

    @Test
    fun testRunTestWithIllegalContext() {
        for (ctx in TestScopeTest.invalidContexts) {
            assertFailsWith<IllegalArgumentException> {
                runTestWithLegacyScope(ctx) { }
            }
        }
    }

    @Test
    fun testThrowingInRunTestBody() = testResultMap({
        assertFailsWith<RuntimeException> { it() }
    }) {
        runTestWithLegacyScope {
            throw RuntimeException()
        }
    }

    @Test
    fun testThrowingInRunTestPendingTask() = testResultMap({
        assertFailsWith<RuntimeException> { it() }
    }) {
        runTestWithLegacyScope {
            launch {
                delay(SLOW)
                throw RuntimeException()
            }
        }
    }

    @Test
    fun reproducer2405() = runTestWithLegacyScope {
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

    @Test
    fun testChildrenCancellationOnTestBodyFailure(): TestResult {
        var job: Job? = null
        return testResultMap({
            assertFailsWith<AssertionError> { it() }
            assertTrue(job!!.isCancelled)
        }) {
            runTestWithLegacyScope {
                job = launch {
                    while (true) {
                        delay(1000)
                    }
                }
                throw AssertionError()
            }
        }
    }

    @Test
    fun testTimeout() = testResultMap({
        assertFailsWith<TimeoutCancellationException> { it() }
    }) {
        runTestWithLegacyScope {
            withTimeout(50) {
                launch {
                    delay(1000)
                }
            }
        }
    }

    @Test
    fun testRunTestThrowsRootCause() = testResultMap({
        assertFailsWith<TestException> { it() }
    }) {
        runTestWithLegacyScope {
            launch {
                throw TestException()
            }
        }
    }

    @Test
    fun testCompletesOwnJob(): TestResult {
        var handlerCalled = false
        return testResultMap({
            it()
            assertTrue(handlerCalled)
        }) {
            runTestWithLegacyScope {
                coroutineContext.job.invokeOnCompletion {
                    handlerCalled = true
                }
            }
        }
    }

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
            runTestWithLegacyScope(job) {
                assertTrue(coroutineContext.job in job.children)
            }
        }
    }

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
        runTestWithLegacyScope {
            launch(SupervisorJob()) { throw TestException("x") }
            launch(SupervisorJob()) { throw TestException("y") }
            launch(SupervisorJob()) { throw TestException("z") }
            throw TestException("w")
        }
    }

    @Test
    fun testScopeRunTestExceptionHandler(): TestResult {
        val scope = TestCoroutineScope()
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
