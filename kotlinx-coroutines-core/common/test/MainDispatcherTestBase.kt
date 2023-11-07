/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

abstract class MainDispatcherTestBase: TestBase() {

    open fun shouldSkipTesting(): Boolean = false

    open fun checkIsMainThread() {}

    open fun checkNotMainThread() {}

    /** Runs the given block as a test, unless [shouldSkipTesting] indicates that the environment is not suitable. */
    fun runTestOrSkip(block: suspend CoroutineScope.() -> Unit): TestResult {
        // written as a block body to make the need to return `TestResult` explicit
        return runTest {
            if (shouldSkipTesting()) return@runTest
            block()
        }
    }

    /** Tests the [toString] behavior of [Dispatchers.Main] and [MainCoroutineDispatcher.immediate] */
    @Test
    fun testMainDispatcherToString() {
        // TODO: workaround for not having module-info.java for the `test` source set
        if (Dispatchers.Main.toString() != "Dispatchers.Main") {
            throw AssertionError("Expected Dispatchers.Main, but had ${Dispatchers.Main}")
        }
        if (Dispatchers.Main.immediate.toString() != "Dispatchers.Main.immediate") {
            throw AssertionError("Expected Dispatchers.Main.immediate, but had ${Dispatchers.Main.immediate}")
        }
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
        // TODO: workaround for not having module-info.java for the `test` source set
        if (Dispatchers.Main == Dispatchers.Main.immediate) {
            throw AssertionError("Expected Dispatchers.Main and Dispatchers.Main.immediate not to be equal")
        }
    }

    /** Tests that after a delay, the execution gets back to the main thread. */
    @Test
    @Ignore // TODO: hangs on Android
    fun testDelay() = runTestOrSkip {
        expect(1)
        withContext(Dispatchers.Main) {
            checkIsMainThread()
            expect(2)
            delay(100)
            checkIsMainThread()
            expect(3)
        }
        finish(4)
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
            finish(5)
        }
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
}
