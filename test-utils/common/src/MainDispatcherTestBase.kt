package kotlinx.coroutines.testing

import kotlinx.coroutines.*
import kotlin.test.*

abstract class MainDispatcherTestBase: TestBase() {

    open fun shouldSkipTesting(): Boolean = false

    open suspend fun spinTest(testBody: Job) {
        testBody.join()
    }

    abstract fun isMainThread(): Boolean?

    /** Runs the given block as a test, unless [shouldSkipTesting] indicates that the environment is not suitable. */
    fun runTestOrSkip(block: suspend CoroutineScope.() -> Unit): TestResult {
        // written as a block body to make the need to return `TestResult` explicit
        return runTest {
            if (shouldSkipTesting()) return@runTest
            val testBody = launch(Dispatchers.Default) {
                block()
            }
            spinTest(testBody)
        }
    }

    /** Tests the [toString] behavior of [Dispatchers.Main] and [MainCoroutineDispatcher.immediate] */
    @Test
    fun testMainDispatcherToString() {
        assertEquals("Dispatchers.Main", Dispatchers.Main.toString())
        assertEquals("Dispatchers.Main.immediate", Dispatchers.Main.immediate.toString())
    }

    /** Tests that the tasks scheduled earlier from [MainCoroutineDispatcher.immediate] will be executed earlier,
     * even if the immediate dispatcher was entered from the main thread. */
    @Test
    fun testMainDispatcherOrderingInMainThread() = runTestOrSkip {
        withContext(Dispatchers.Main) {
            testMainDispatcherOrdering()
        }
    }

    /** Tests that the tasks scheduled earlier from [MainCoroutineDispatcher.immediate] will be executed earlier
     * if the immediate dispatcher was entered from outside the main thread. */
    @Test
    fun testMainDispatcherOrderingOutsideMainThread() = runTestOrSkip {
        testMainDispatcherOrdering()
    }

    /** Tests that [Dispatchers.Main] and its [MainCoroutineDispatcher.immediate] are treated as different values. */
    @Test
    fun testHandlerDispatcherNotEqualToImmediate() {
        assertNotEquals(Dispatchers.Main, Dispatchers.Main.immediate)
    }

    /** Tests that [Dispatchers.Main] shares its queue with [MainCoroutineDispatcher.immediate]. */
    @Test
    fun testImmediateDispatcherYield() = runTestOrSkip {
        withContext(Dispatchers.Main) {
            expect(1)
            checkIsMainThread()
            // launch in the immediate dispatcher
            launch(Dispatchers.Main.immediate) {
                expect(2)
                yield()
                expect(4)
            }
            expect(3) // after yield
            yield() // yield back
            expect(5)
        }
        finish(6)
    }

    /** Tests that entering [MainCoroutineDispatcher.immediate] from [Dispatchers.Main] happens immediately. */
    @Test
    fun testEnteringImmediateFromMain() = runTestOrSkip {
        withContext(Dispatchers.Main) {
            expect(1)
            val job = launch { expect(3) }
            withContext(Dispatchers.Main.immediate) {
                expect(2)
            }
            job.join()
        }
        finish(4)
    }

    /** Tests that dispatching to [MainCoroutineDispatcher.immediate] is required from and only from dispatchers
     * other than the main dispatchers and that it's always required for [Dispatchers.Main] itself. */
    @Test
    fun testDispatchRequirements() = runTestOrSkip {
        checkDispatchRequirements()
        withContext(Dispatchers.Main) {
            checkDispatchRequirements()
            withContext(Dispatchers.Main.immediate) {
                checkDispatchRequirements()
            }
            checkDispatchRequirements()
        }
        checkDispatchRequirements()
    }

    private suspend fun checkDispatchRequirements() {
        isMainThread()?.let {
            assertNotEquals(
                it,
                Dispatchers.Main.immediate.isDispatchNeeded(currentCoroutineContext())
            )
        }
        assertTrue(Dispatchers.Main.isDispatchNeeded(currentCoroutineContext()))
        assertTrue(Dispatchers.Default.isDispatchNeeded(currentCoroutineContext()))
    }

    /** Tests that launching a coroutine in [MainScope] will execute it in the main thread. */
    @Test
    fun testLaunchInMainScope() = runTestOrSkip {
        var executed = false
        withMainScope {
            launch {
                checkIsMainThread()
                executed = true
            }.join()
            if (!executed) throw AssertionError("Should be executed")
        }
    }

    /** Tests that a failure in [MainScope] will not propagate upwards. */
    @Test
    fun testFailureInMainScope() = runTestOrSkip {
        var exception: Throwable? = null
        withMainScope {
            launch(CoroutineExceptionHandler { ctx, e -> exception = e }) {
                checkIsMainThread()
                throw TestException()
            }.join()
        }
        if (exception!! !is TestException) throw AssertionError("Expected TestException, but had $exception")
    }

    /** Tests cancellation in [MainScope]. */
    @Test
    fun testCancellationInMainScope() = runTestOrSkip {
        withMainScope {
            cancel()
            launch(start = CoroutineStart.ATOMIC) {
                checkIsMainThread()
                delay(Long.MAX_VALUE)
            }.join()
        }
    }

    private suspend fun <R> withMainScope(block: suspend CoroutineScope.() -> R): R {
        MainScope().apply {
            return block().also { coroutineContext[Job]!!.cancelAndJoin() }
        }
    }

    private suspend fun testMainDispatcherOrdering() {
        withContext(Dispatchers.Main.immediate) {
            expect(1)
            launch(Dispatchers.Main) {
                expect(2)
            }
            withContext(Dispatchers.Main) {
                finish(3)
            }
        }
    }

    abstract class WithRealTimeDelay : MainDispatcherTestBase() {
        abstract fun scheduleOnMainQueue(block: () -> Unit)

        /** Tests that after a delay, the execution gets back to the main thread. */
        @Test
        fun testDelay() = runTestOrSkip {
            expect(1)
            checkNotMainThread()
            scheduleOnMainQueue { expect(2) }
            withContext(Dispatchers.Main) {
                checkIsMainThread()
                expect(3)
                scheduleOnMainQueue { expect(4) }
                delay(100)
                checkIsMainThread()
                expect(5)
            }
            checkNotMainThread()
            finish(6)
        }

        /** Tests that [Dispatchers.Main] is in agreement with the default time source: it's not much slower. */
        @Test
        fun testWithTimeoutContextDelayNoTimeout() = runTestOrSkip {
            expect(1)
            withTimeout(1000) {
                withContext(Dispatchers.Main) {
                    checkIsMainThread()
                    expect(2)
                    delay(100)
                    checkIsMainThread()
                    expect(3)
                }
            }
            checkNotMainThread()
            finish(4)
        }

        /** Tests that [Dispatchers.Main] is in agreement with the default time source: it's not much faster. */
        @Test
        fun testWithTimeoutContextDelayTimeout() = runTestOrSkip {
            expect(1)
            assertFailsWith<TimeoutCancellationException> {
                withTimeout(300) {
                    // A substitute for withContext(Dispatcher.Main) that is started even if the 300ms
                    // timeout happens fsater then dispatch
                    launch(Dispatchers.Main, start = CoroutineStart.ATOMIC) {
                        checkIsMainThread()
                        expect(2)
                        delay(1000)
                        expectUnreached()
                    }.join()
                }
                expectUnreached()
            }
            checkNotMainThread()
            finish(3)
        }

        /** Tests that the timeout of [Dispatchers.Main] is in agreement with its [delay]: it's not much faster. */
        @Test
        fun testWithContextTimeoutDelayNoTimeout() = runTestOrSkip {
            expect(1)
            withContext(Dispatchers.Main) {
                withTimeout(1000) {
                    checkIsMainThread()
                    expect(2)
                    delay(100)
                    checkIsMainThread()
                    expect(3)
                }
            }
            checkNotMainThread()
            finish(4)
        }

        /** Tests that the timeout of [Dispatchers.Main] is in agreement with its [delay]: it's not much slower. */
        @Test
        fun testWithContextTimeoutDelayTimeout() = runTestOrSkip {
            expect(1)
            assertFailsWith<TimeoutCancellationException> {
                withContext(Dispatchers.Main) {
                    withTimeout(100) {
                        checkIsMainThread()
                        expect(2)
                        delay(1000)
                        expectUnreached()
                    }
                }
                expectUnreached()
            }
            checkNotMainThread()
            finish(3)
        }
    }

    fun checkIsMainThread() { isMainThread()?.let { check(it) } }
    fun checkNotMainThread() { isMainThread()?.let { check(!it) } }
}
