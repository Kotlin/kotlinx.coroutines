/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.test

import kotlinx.coroutines.experimental.*
import org.junit.After
import org.junit.Assert.*
import org.junit.Test

class TestCoroutineContextTest {
    private val injectedContext = TestCoroutineContext()

    @After
    fun tearDown() {
        injectedContext.cancelAllActions()
    }

    @Test
    fun testDelayWithLaunch() = withTestContext(injectedContext) {
        val delay = 1000L

        var executed = false
        launch {
            suspendedDelayedAction(delay) {
                executed = true
            }
        }

        advanceTimeBy(delay / 2)
        assertFalse(executed)

        advanceTimeBy(delay / 2)
        assertTrue(executed)
    }

    @Test
    fun testTimeJumpWithLaunch() = withTestContext(injectedContext) {
        val delay = 1000L

        var executed = false
        launch {
            suspendedDelayedAction(delay) {
                executed = true
            }
        }

        advanceTimeTo(delay / 2)
        assertFalse(executed)

        advanceTimeTo(delay)
        assertTrue(executed)
    }

    @Test
    fun testDelayWithAsync() = withTestContext(injectedContext) {
        val delay = 1000L

        var executed = false
        async {
            suspendedDelayedAction(delay) {
                executed = true
            }
        }

        advanceTimeBy(delay / 2)
        assertFalse(executed)

        advanceTimeBy(delay / 2)
        assertTrue(executed)
    }

    @Test
    fun testDelayWithRunBlocking() = withTestContext(injectedContext) {
        val delay = 1000L

        var executed = false
        runBlocking {
            suspendedDelayedAction(delay) {
                executed = true
            }
        }

        assertTrue(executed)
        assertEquals(delay, now())
    }

    private suspend fun suspendedDelayedAction(delay: Long, action: () -> Unit) {
        delay(delay)
        action()
    }

    @Test
    fun testDelayedFunctionWithRunBlocking() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedValue = 16

        val result = runBlocking {
            suspendedDelayedFunction(delay) {
                expectedValue
            }
        }

        assertEquals(expectedValue, result)
        assertEquals(delay, now())
    }

    @Test
    fun testDelayedFunctionWithAsync() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedValue = 16

        val deferred = async {
            suspendedDelayedFunction(delay) {
                expectedValue
            }
        }

        advanceTimeBy(delay / 2)
        try {
            deferred.getCompleted()
            fail("The Job should not have been completed yet.")
        } catch (e: Exception) {
            // Success.
        }

        advanceTimeBy(delay / 2)
        assertEquals(expectedValue, deferred.getCompleted())
    }

    private suspend fun <T> TestCoroutineContext.suspendedDelayedFunction(delay: Long, function: () -> T): T {
        delay(delay / 4)
        return async {
            delay((delay / 4) * 3)
            function()
        }.await()
    }

    @Test
    fun testBlockingFunctionWithRunBlocking() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedValue = 16

        val result = runBlocking {
            suspendedBlockingFunction(delay) {
                expectedValue
            }
        }

        assertEquals(expectedValue, result)
        assertEquals(delay, now())
    }

    @Test
    fun testBlockingFunctionWithAsync() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedValue = 16
        var now = 0L

        val deferred = async {
            suspendedBlockingFunction(delay) {
                expectedValue
            }
        }

        now += advanceTimeBy((delay / 4) - 1)
        assertEquals((delay / 4) - 1, now)
        assertEquals(now, now())
        try {
            deferred.getCompleted()
            fail("The Job should not have been completed yet.")
        } catch (e: Exception) {
            // Success.
        }

        now += advanceTimeBy(1)
        assertEquals(delay, now())
        assertEquals(now, now())
        assertEquals(expectedValue, deferred.getCompleted())
    }

    private suspend fun <T> TestCoroutineContext.suspendedBlockingFunction(delay: Long, function: () -> T): T {
        delay(delay / 4)
        return runBlocking {
            delay((delay / 4) * 3)
            function()
        }
    }

    @Test
    fun testTimingOutFunctionWithAsyncAndNoTimeout() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedValue = 67

        val result = async {
            suspendedTimingOutFunction(delay, delay + 1) {
                expectedValue
            }
        }

        triggerActions()
        assertEquals(expectedValue, result.getCompleted())
    }

    @Test
    fun testTimingOutFunctionWithAsyncAndTimeout() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedValue = 67

        val result = async {
            suspendedTimingOutFunction(delay, delay) {
                expectedValue
            }
        }

        triggerActions()
        assertTrue(result.getCompletionExceptionOrNull() is TimeoutCancellationException)
    }

    @Test
    fun testTimingOutFunctionWithRunBlockingAndTimeout() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedValue = 67

        try {
            runBlocking {
                suspendedTimingOutFunction(delay, delay) {
                    expectedValue
                }
            }
            fail("Expected TimeoutCancellationException to be thrown.")
        } catch (e: TimeoutCancellationException) {
            // Success
        } catch (e: Throwable) {
            fail("Expected TimeoutCancellationException to be thrown: $e")
        }
    }

    private suspend fun <T> TestCoroutineContext.suspendedTimingOutFunction(delay: Long, timeOut: Long, function: () -> T): T {
        return runBlocking {
            withTimeout(timeOut) {
                delay(delay / 2)
                val ret = function()
                delay(delay / 2)
                ret
            }
        }
    }

    @Test(expected = AssertionError::class)
    fun testWithTestContextThrowingAnAssertionError() = withTestContext(injectedContext) {
        val expectedError = IllegalAccessError("hello")

        launch {
            throw expectedError
        }

        triggerActions()
    }

    @Test
    fun testExceptionHandlingWithLaunch() = withTestContext(injectedContext) {
        val expectedError = IllegalAccessError("hello")

        launch {
            throw expectedError
        }

        triggerActions()
        assertUnhandledException { it === expectedError}
    }

    @Test
    fun testExceptionHandlingWithLaunchingChildCoroutines() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedError = IllegalAccessError("hello")
        val expectedValue = 12

        launch {
            suspendedAsyncWithExceptionAfterDelay(delay, expectedError, expectedValue, true)
        }

        advanceTimeBy(delay)
        assertUnhandledException { it === expectedError}
    }

    @Test
    fun testExceptionHandlingWithAsyncAndDontWaitForException() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedError = IllegalAccessError("hello")
        val expectedValue = 12

        val result = async {
            suspendedAsyncWithExceptionAfterDelay(delay, expectedError, expectedValue, false)
        }

        advanceTimeBy(delay)

        assertNull(result.getCompletionExceptionOrNull())
        assertEquals(expectedValue, result.getCompleted())
    }

    @Test
    fun testExceptionHandlingWithAsyncAndWaitForException() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedError = IllegalAccessError("hello")
        val expectedValue = 12

        val result = async {
            suspendedAsyncWithExceptionAfterDelay(delay, expectedError, expectedValue, true)
        }

        advanceTimeBy(delay)

        val e = result.getCompletionExceptionOrNull()
        assertTrue("Expected to be thrown: '$expectedError' but was '$e'", expectedError === e)
    }

    @Test
    fun testExceptionHandlingWithRunBlockingAndDontWaitForException() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedError = IllegalAccessError("hello")
        val expectedValue = 12

        val result = runBlocking {
            suspendedAsyncWithExceptionAfterDelay(delay, expectedError, expectedValue, false)
        }

        advanceTimeBy(delay)

        assertEquals(expectedValue, result)
    }

    @Test
    fun testExceptionHandlingWithRunBlockingAndWaitForException() = withTestContext(injectedContext) {
        val delay = 1000L
        val expectedError = IllegalAccessError("hello")
        val expectedValue = 12

        try {
            runBlocking {
                suspendedAsyncWithExceptionAfterDelay(delay, expectedError, expectedValue, true)
            }
            fail("Expected to be thrown: '$expectedError'")
        } catch (e: AssertionError) {
            throw e
        } catch (e: Throwable) {
            assertTrue("Expected to be thrown: '$expectedError' but was '$e'", expectedError === e)
        }
    }

    private suspend fun <T> TestCoroutineContext.suspendedAsyncWithExceptionAfterDelay(delay: Long, exception: Throwable, value: T, await: Boolean): T {
        val deferred = async {
            delay(delay - 1)
            throw exception
        }

        if (await) {
            deferred.await()
        }
        return value
    }

    @Test
    fun testCancellationException() = withTestContext {
        val job = launch {
            delay(1000)
        }

        advanceTimeBy(500)
        assertTrue(job.cancel())

        assertAllUnhandledExceptions { it is CancellationException }
    }

    @Test
    fun testCancellationExceptionNotThrownByWithTestContext() = withTestContext {
        val job = launch {
            delay(1000)
        }

        advanceTimeBy(500)
        assertTrue(job.cancel())
    }
}


/* Some helper functions */
private fun TestCoroutineContext.launch(
        start: CoroutineStart = CoroutineStart.DEFAULT,
        parent: Job? = null,
        onCompletion: CompletionHandler? = null,
        block: suspend CoroutineScope.() -> Unit
) = launch(this, start, parent, onCompletion, block)

private fun <T> TestCoroutineContext.async(
        start: CoroutineStart = CoroutineStart.DEFAULT,
        parent: Job? = null,
        onCompletion: CompletionHandler? = null,
        block: suspend CoroutineScope.() -> T

) = async(this, start, parent, onCompletion, block)

private fun <T> TestCoroutineContext.runBlocking(
        block: suspend CoroutineScope.() -> T
) = runBlocking(this, block)
