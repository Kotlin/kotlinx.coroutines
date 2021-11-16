/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
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
}