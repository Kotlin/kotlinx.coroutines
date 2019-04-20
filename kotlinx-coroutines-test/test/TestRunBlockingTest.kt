/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.Assert.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class TestRunBlockingTest {

    @Test
    fun delay_advancesTimeAutomatically() = runBlockingTest {
        assertRunsFast {
            delay(SLOW)
        }
    }

    @Test
    fun callingSuspendWithDelay_advancesAutomatically() = runBlockingTest {
        suspend fun withDelay(): Int {
            delay(SLOW)
            return 3
        }

        assertRunsFast {
            assertEquals(3, withDelay())
        }
    }

    @Test
    fun launch_advancesAutomatically()  = runBlockingTest {
        val job = launch {
            delay(SLOW)
        }
        assertRunsFast {
            job.join()
            assertTrue(job.isCompleted)
        }
    }

    @Test
    fun async_advancesAutomatically() = runBlockingTest {
        val deferred = async {
            delay(SLOW)
            3
        }

        assertRunsFast {
            assertEquals(3, deferred.await())
        }
    }

    @Test
    fun incorrectlyCalledRunblocking_doesNotHaveSameInterceptor() = runBlockingTest {
        // this code is an error as a production test, please do not use this as an example

        // this test exists to document this error condition, if it's possible to make this code work please update
        val outerInterceptor = coroutineContext[ContinuationInterceptor]
        // runBlocking always requires an argument to pass the context in tests
        runBlocking {
            assertNotSame(coroutineContext[ContinuationInterceptor], outerInterceptor)
        }
    }

    @Test(expected = TimeoutCancellationException::class)
    fun whenUsingTimeout_triggersWhenDelayed() = runBlockingTest {
        assertRunsFast {
            withTimeout(SLOW) {
                delay(SLOW)
            }
        }
    }

    @Test
    fun whenUsingTimeout_doesNotTriggerWhenFast() = runBlockingTest {
        assertRunsFast {
            withTimeout(SLOW) {
                delay(0)
            }
        }
    }

    @Test(expected = TimeoutCancellationException::class)
    fun whenUsingTimeout_triggersWhenWaiting() = runBlockingTest {
        val uncompleted = CompletableDeferred<Unit>()
        assertRunsFast {
            withTimeout(SLOW) {
                uncompleted.await()
            }
        }
    }

    @Test
    fun whenUsingTimeout_doesNotTriggerWhenComplete() = runBlockingTest {
        val completed = CompletableDeferred<Unit>()
        assertRunsFast {
            completed.complete(Unit)
            withTimeout(SLOW) {
                completed.await()
            }
        }
    }

    @Test
    fun testDelayInAsync_withAwait() = runBlockingTest {
        assertRunsFast {
            val deferred = async {
                delay(SLOW)
                3
            }
            assertEquals(3, deferred.await())
        }
    }

    @Test(expected = TimeoutCancellationException::class)
    fun whenUsingTimeout_inAsync_triggersWhenDelayed() = runBlockingTest {
        val deferred = async {
            withTimeout(SLOW) {
                delay(SLOW)
            }
        }

        assertRunsFast {
            deferred.await()
        }
    }

    @Test
    fun whenUsingTimeout_inAsync_doesNotTriggerWhenNotDelayed() = runBlockingTest {
        val testScope = this
        val deferred = async {
            withTimeout(SLOW) {
                delay(0)
            }
        }

        assertRunsFast {
            deferred.await()
        }
    }

    @Test(expected = TimeoutCancellationException::class)
    fun whenUsingTimeout_inLaunch_triggersWhenDelayed() = runBlockingTest {
        val job= launch {
            withTimeout(1) {
                delay(SLOW + 1)
                3
            }
        }

        assertRunsFast {
            job.join()
            throw job.getCancellationException()
        }
    }

    @Test
    fun whenUsingTimeout_inLaunch_doesNotTriggerWhenNotDelayed() = runBlockingTest {
        val job = launch {
            withTimeout(SLOW) {
                delay(0)
            }
        }

        assertRunsFast {
            job.join()
            assertTrue(job.isCompleted)
        }
    }

    @Test(expected = IllegalArgumentException::class)
    fun throwingException_throws() = runBlockingTest {
        assertRunsFast {
            delay(SLOW)
            throw IllegalArgumentException("Test")
        }
    }

    @Test(expected = IllegalArgumentException::class)
    fun throwingException_inLaunch_throws() = runBlockingTest {
        val job = launch {
            delay(SLOW)
            throw IllegalArgumentException("Test")
        }

        assertRunsFast {
            job.join()
            throw job.getCancellationException().cause ?: assertFails { "expected exception" }
        }
    }

    @Test(expected = IllegalArgumentException::class)
    fun throwingException__inAsync_throws() = runBlockingTest {
        val deferred = async {
            delay(SLOW)
            throw IllegalArgumentException("Test")
        }

        assertRunsFast {
            deferred.await()
        }
    }

    @Test
    fun callingLaunchFunction_executesLaunchBlockImmediately() = runBlockingTest {
        assertRunsFast {
            var executed = false
            launch {
                delay(SLOW)
                executed = true
            }

            delay(SLOW)
            assertTrue(executed)
        }
    }

    @Test
    fun callingAsyncFunction_executesAsyncBlockImmediately() = runBlockingTest {
        assertRunsFast {
            var executed = false
            async {
                delay(SLOW)
                executed = true
            }
            advanceTimeBy(SLOW)

            assertTrue(executed)
        }
    }

    @Test
    fun nestingBuilders_executesSecondLevelImmediately() = runBlockingTest {
        assertRunsFast {
            var levels = 0
            launch {
                delay(SLOW)
                levels++
                launch {
                    delay(SLOW)
                    levels++
                }
            }
            advanceUntilIdle()

            assertEquals(2, levels)
        }
    }

    @Test
    fun testCancellationException() = runBlockingTest {
        var actual: CancellationException? = null
        val uncompleted = CompletableDeferred<Unit>()
        val job = launch {
            actual = kotlin.runCatching { uncompleted.await() }.exceptionOrNull() as? CancellationException
        }

        assertNull(actual)
        job.cancel()
        assertNotNull(actual)
    }

    @Test
    fun testCancellationException_notThrown() = runBlockingTest {
        val uncompleted = CompletableDeferred<Unit>()
        val job = launch {
            uncompleted.await()
        }

        job.cancel()
        job.join()
    }

    @Test(expected = UncompletedCoroutinesError::class)
    fun whenACoroutineLeaks_errorIsThrown() = runBlockingTest {
        val uncompleted = CompletableDeferred<Unit>()
        launch {
            uncompleted.await()
        }
    }

    @Test(expected = java.lang.IllegalArgumentException::class)
    fun runBlockingTestBuilder_throwsOnBadDispatcher() {
        runBlockingTest(newSingleThreadContext("name")) {

        }
    }

    @Test(expected = java.lang.IllegalArgumentException::class)
    fun runBlockingTestBuilder_throwsOnBadHandler() {
        runBlockingTest(CoroutineExceptionHandler { _, _ -> Unit} ) {

        }
    }

    @Test
    fun pauseDispatcher_disablesAutoAdvance_forCurrent() = runBlockingTest {
        var mutable = 0
        pauseDispatcher {
            launch {
                mutable++
            }
            assertEquals(0, mutable)
            runCurrent()
            assertEquals(1, mutable)
        }
    }

    @Test
    fun pauseDispatcher_disablesAutoAdvance_forDelay() = runBlockingTest {
        var mutable = 0
        pauseDispatcher {
            launch {
                mutable++
                delay(SLOW)
                mutable++
            }
            assertEquals(0, mutable)
            runCurrent()
            assertEquals(1, mutable)
            advanceTimeBy(SLOW)
            assertEquals(2, mutable)
        }
    }

    @Test
    fun pauseDispatcher_withDelay_resumesAfterPause() = runBlockingTest {
        var mutable = 0
        assertRunsFast {
            pauseDispatcher {
                delay(1_000)
                mutable++
            }
        }
        assertEquals(1, mutable)
    }


    @Test(expected = IllegalAccessError::class)
    fun testWithTestContextThrowingAnAssertionError() = runBlockingTest {
        val expectedError = IllegalAccessError("hello")

        val job = launch {
            throw expectedError
        }

        // don't rethrow or handle the exception
    }

    @Test(expected = IllegalAccessError::class)
    fun testExceptionHandlingWithLaunch() = runBlockingTest {
        val expectedError = IllegalAccessError("hello")

        launch {
            throw expectedError
        }
    }

    @Test(expected = IllegalAccessError::class)
    fun testExceptions_notThrownImmediately() = runBlockingTest {
        val expectedException = IllegalAccessError("hello")
        val result = runCatching {
            launch {
                throw expectedException
            }
        }
        runCurrent()
        assertEquals(true, result.isSuccess)
    }
}