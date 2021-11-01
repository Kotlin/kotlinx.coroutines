/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.test.*

@Suppress("DEPRECATION")
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
    fun whenUsingTimeout_triggersWhenDelayed() {
        assertFailsWith<TimeoutCancellationException> {
            runBlockingTest {
                assertRunsFast {
                    withTimeout(SLOW) {
                        delay(SLOW)
                    }
                }
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

    @Test
    fun whenUsingTimeout_triggersWhenWaiting() {
        assertFailsWith<TimeoutCancellationException> {
            runBlockingTest {
                val uncompleted = CompletableDeferred<Unit>()
                assertRunsFast {
                    withTimeout(SLOW) {
                        uncompleted.await()
                    }
                }
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

    @Test
    fun whenUsingTimeout_inAsync_triggersWhenDelayed() {
        assertFailsWith<TimeoutCancellationException> {
            runBlockingTest {
                val deferred = async {
                    withTimeout(SLOW) {
                        delay(SLOW)
                    }
                }

                assertRunsFast {
                    deferred.await()
                }
            }
        }
    }

    @Test
    fun whenUsingTimeout_inAsync_doesNotTriggerWhenNotDelayed() = runBlockingTest {
        val deferred = async {
            withTimeout(SLOW) {
                delay(0)
            }
        }

        assertRunsFast {
            deferred.await()
        }
    }

    @Test
    fun whenUsingTimeout_inLaunch_triggersWhenDelayed() {
        assertFailsWith<TimeoutCancellationException> {
            runBlockingTest {
                val job = launch {
                    withTimeout(1) {
                        delay(SLOW + 1)
                    }
                }

                assertRunsFast {
                    job.join()
                    throw job.getCancellationException()
                }
            }
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

    @Test
    fun throwingException_throws() {
        assertFailsWith<IllegalArgumentException> {
            runBlockingTest {
                assertRunsFast {
                    delay(SLOW)
                    throw IllegalArgumentException("Test")
                }
            }
        }
    }

    @Test
    fun throwingException_inLaunch_throws() {
        assertFailsWith<IllegalArgumentException> {
            runBlockingTest {
                val job = launch {
                    delay(SLOW)
                    throw IllegalArgumentException("Test")
                }

                assertRunsFast {
                    job.join()
                    throw job.getCancellationException().cause ?: AssertionError("expected exception")
                }
            }
        }
    }

    @Test
    fun throwingException__inAsync_throws() {
        assertFailsWith<IllegalArgumentException> {
            runBlockingTest {
                val deferred: Deferred<Unit> = async {
                    delay(SLOW)
                    throw IllegalArgumentException("Test")
                }

                assertRunsFast {
                    deferred.await()
                }
            }
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
            val deferred = async {
                delay(SLOW)
                executed = true
            }
            advanceTimeBy(SLOW)

            assertTrue(deferred.isCompleted)
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

    @Test
    fun whenACoroutineLeaks_errorIsThrown() {
        assertFailsWith<UncompletedCoroutinesError> {
            runBlockingTest {
                val uncompleted = CompletableDeferred<Unit>()
                launch {
                    uncompleted.await()
                }
            }
        }
    }

    @Test
    fun runBlockingTestBuilder_throwsOnBadDispatcher() {
        assertFailsWith<IllegalArgumentException> {
            runBlockingTest(Dispatchers.Default) {

            }
        }
    }

    @Test
    fun runBlockingTestBuilder_throwsOnBadHandler() {
        assertFailsWith<IllegalArgumentException> {
            runBlockingTest(CoroutineExceptionHandler { _, _ -> }) {

            }
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


    @Test
    fun testWithTestContextThrowingAnAssertionError() {
        assertFailsWith<TestException> {
            runBlockingTest {
                val expectedError = TestException("hello")

                launch {
                    throw expectedError
                }

                // don't rethrow or handle the exception
            }
        }
    }

    @Test
    fun testExceptionHandlingWithLaunch() {
        assertFailsWith<TestException> {
            runBlockingTest {
                val expectedError = TestException("hello")

                launch {
                    throw expectedError
                }
            }
        }
    }

    @Test
    fun testExceptions_notThrownImmediately() {
        assertFailsWith<TestException> {
            runBlockingTest {
                val expectedException = TestException("hello")
                val result = runCatching {
                    launch {
                        throw expectedException
                    }
                }
                runCurrent()
                assertEquals(true, result.isSuccess)
            }
        }
    }


    private val exceptionHandler = TestCoroutineExceptionHandler()

    @Test
    fun testPartialContextOverride() = runBlockingTest(CoroutineName("named")) {
        assertEquals(CoroutineName("named"), coroutineContext[CoroutineName])
        assertNotNull(coroutineContext[CoroutineExceptionHandler])
        assertNotSame(coroutineContext[CoroutineExceptionHandler], exceptionHandler)
    }

    @Test
    fun testPartialDispatcherOverride() {
        assertFailsWith<IllegalArgumentException> {
            runBlockingTest(Dispatchers.Unconfined) {
                fail("Unreached")
            }
        }
    }

    @Test
    fun testOverrideExceptionHandler() = runBlockingTest(exceptionHandler) {
        assertSame(coroutineContext[CoroutineExceptionHandler], exceptionHandler)
    }

    @Test
    fun testOverrideExceptionHandlerError() {
        assertFailsWith<IllegalArgumentException> {
            runBlockingTest(CoroutineExceptionHandler { _, _ -> }) {
                fail("Unreached")
            }
        }
    }
}