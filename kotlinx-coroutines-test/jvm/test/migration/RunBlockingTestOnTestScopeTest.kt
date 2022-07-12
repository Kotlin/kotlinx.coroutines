/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

/** Copy of [RunTestTest], but for [runBlockingTestOnTestScope], where applicable. */
@Suppress("DEPRECATION")
class RunBlockingTestOnTestScopeTest {

    @Test
    fun testRunTestWithIllegalContext() {
        for (ctx in TestScopeTest.invalidContexts) {
            assertFailsWith<IllegalArgumentException> {
                runBlockingTestOnTestScope(ctx) { }
            }
        }
    }

    @Test
    fun testThrowingInRunTestBody() {
        assertFailsWith<RuntimeException> {
            runBlockingTestOnTestScope {
                throw RuntimeException()
            }
        }
    }

    @Test
    fun testThrowingInRunTestPendingTask() {
        assertFailsWith<RuntimeException> {
            runBlockingTestOnTestScope {
                launch {
                    delay(SLOW)
                    throw RuntimeException()
                }
            }
        }
    }

    @Test
    fun reproducer2405() = runBlockingTestOnTestScope {
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
    fun testChildrenCancellationOnTestBodyFailure() {
        var job: Job? = null
        assertFailsWith<AssertionError> {
            runBlockingTestOnTestScope {
                job = launch {
                    while (true) {
                        delay(1000)
                    }
                }
                throw AssertionError()
            }
        }
        assertTrue(job!!.isCancelled)
    }

    @Test
    fun testTimeout() {
        assertFailsWith<TimeoutCancellationException> {
            runBlockingTestOnTestScope {
                withTimeout(50) {
                    launch {
                        delay(1000)
                    }
                }
            }
        }
    }

    @Test
    fun testRunTestThrowsRootCause() {
        assertFailsWith<TestException> {
            runBlockingTestOnTestScope {
                launch {
                    throw TestException()
                }
            }
        }
    }

    @Test
    fun testCompletesOwnJob() {
        var handlerCalled = false
        runBlockingTestOnTestScope {
            coroutineContext.job.invokeOnCompletion {
                handlerCalled = true
            }
        }
        assertTrue(handlerCalled)
    }

    @Test
    fun testDoesNotCompleteGivenJob() {
        var handlerCalled = false
        val job = Job()
        job.invokeOnCompletion {
            handlerCalled = true
        }
        runBlockingTestOnTestScope(job) {
            assertTrue(coroutineContext.job in job.children)
        }
        assertFalse(handlerCalled)
        assertEquals(0, job.children.filter { it.isActive }.count())
    }

    @Test
    fun testSuppressedExceptions() {
        try {
            runBlockingTestOnTestScope {
                launch(SupervisorJob()) { throw TestException("x") }
                launch(SupervisorJob()) { throw TestException("y") }
                launch(SupervisorJob()) { throw TestException("z") }
                throw TestException("w")
            }
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

    @Test
    fun testBackgroundWorkBeingRun() = runBlockingTestOnTestScope {
        var i = 0
        var j = 0
        backgroundScope.launch {
            yield()
            ++i
        }
        backgroundScope.launch {
            yield()
            delay(10)
            ++j
        }
        assertEquals(0, i)
        assertEquals(0, j)
        delay(1)
        assertEquals(1, i)
        assertEquals(0, j)
        delay(10)
        assertEquals(1, i)
        assertEquals(1, j)
    }

    @Test
    fun testBackgroundWorkCancelled() {
        var cancelled = false
        runBlockingTestOnTestScope {
            var i = 0
            backgroundScope.launch {
                yield()
                try {
                    while (isActive) {
                        ++i
                        yield()
                    }
                } catch (e: CancellationException) {
                    cancelled = true
                }
            }
            repeat(5) {
                assertEquals(i, it)
                yield()
            }
        }
        assertTrue(cancelled)
    }

    @Test
    fun testBackgroundWorkTimeControl(): TestResult = runBlockingTestOnTestScope {
        var i = 0
        var j = 0
        backgroundScope.launch {
            yield()
            while (true) {
                ++i
                delay(100)
            }
        }
        backgroundScope.launch {
            yield()
            while (true) {
                ++j
                delay(50)
            }
        }
        advanceUntilIdle() // should do nothing, as only background work is left.
        assertEquals(0, i)
        assertEquals(0, j)
        val job = launch {
            delay(1)
            // the background work scheduled for earlier gets executed before the normal work scheduled for later does
            assertEquals(1, i)
            assertEquals(1, j)
        }
        job.join()
        advanceTimeBy(199) // should work the same for the background tasks
        assertEquals(2, i)
        assertEquals(4, j)
        advanceUntilIdle() // once again, should do nothing
        assertEquals(2, i)
        assertEquals(4, j)
        runCurrent() // should behave the same way as for the normal work
        assertEquals(3, i)
        assertEquals(5, j)
        launch {
            delay(1001)
            assertEquals(13, i)
            assertEquals(25, j)
        }
        advanceUntilIdle() // should execute the normal work, and with that, the background one, too
    }

    @Test
    fun testBackgroundWorkErrorReporting() {
        var testFinished = false
        val exception = RuntimeException("x")
        try {
            runBlockingTestOnTestScope {
                backgroundScope.launch {
                    throw exception
                }
                delay(1000)
                testFinished = true
            }
            fail("unreached")
        } catch (e: Throwable) {
            assertSame(e, exception)
            assertTrue(testFinished)
        }
    }

    @Test
    fun testBackgroundWorkFinalizing() {
        var taskEnded = 0
        val nTasks = 10
        try {
            runBlockingTestOnTestScope {
                repeat(nTasks) {
                    backgroundScope.launch {
                        try {
                            while (true) {
                                delay(1)
                            }
                        } finally {
                            ++taskEnded
                            if (taskEnded <= 2)
                                throw TestException()
                        }
                    }
                }
                delay(100)
                throw TestException()
            }
            fail("unreached")
        } catch (e: TestException) {
            assertEquals(2, e.suppressedExceptions.size)
            assertEquals(nTasks, taskEnded)
        }
    }

    @Test
    fun testExampleBackgroundJob1() = runBlockingTestOnTestScope {
        val myFlow = flow {
            yield()
            var i = 0
            while (true) {
                emit(++i)
                delay(1)
            }
        }
        val stateFlow = myFlow.stateIn(backgroundScope, SharingStarted.Eagerly, 0)
        var j = 0
        repeat(100) {
            assertEquals(j++, stateFlow.value)
            delay(1)
        }
    }

    @Test
    fun testExampleBackgroundJob2() = runBlockingTestOnTestScope {
        val channel = Channel<Int>()
        backgroundScope.launch {
            var i = 0
            while (true) {
                channel.send(i++)
            }
        }
        repeat(100) {
            assertEquals(it, channel.receive())
        }
    }

    @Test
    fun testAsyncFailureInBackgroundReported() =
        try {
            runBlockingTestOnTestScope {
                backgroundScope.async {
                    throw TestException("x")
                }
                backgroundScope.produce<Unit> {
                    throw TestException("y")
                }
                delay(1)
                throw TestException("z")
            }
            fail("unreached")
        } catch (e: TestException) {
            assertEquals("z", e.message)
            assertEquals(setOf("x", "y"), e.suppressedExceptions.map { it.message }.toSet())
        }

    @Test
    fun testNoDuplicateExceptions() =
        try {
            runBlockingTestOnTestScope {
                backgroundScope.launch {
                    throw TestException("x")
                }
                delay(1)
                throw TestException("y")
            }
            fail("unreached")
        } catch (e: TestException) {
            assertEquals("y", e.message)
            assertEquals(listOf("x"), e.suppressedExceptions.map { it.message })
        }
}
