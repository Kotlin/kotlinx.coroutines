/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * A scope which provides detailed control over the execution of coroutines for tests.
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public interface TestCoroutineScope: CoroutineScope, UncaughtExceptionCaptor {
    /**
     * Call after the test completes.
     * Calls [UncaughtExceptionCaptor.cleanupTestCoroutinesCaptor] and [DelayController.cleanupTestCoroutines].
     *
     * @throws Throwable the first uncaught exception, if there are any uncaught exceptions.
     * @throws UncompletedCoroutinesError if any pending tasks are active, however it will not throw for suspended
     * coroutines.
     */
    public fun cleanupTestCoroutines()

    /**
     * The delay-skipping scheduler used by the test dispatchers running the code in this scope.
     */
    @ExperimentalCoroutinesApi
    public val testScheduler: TestCoroutineScheduler

    /**
     * The current virtual time on [testScheduler].
     * @see TestCoroutineScheduler.currentTime
     */
    @ExperimentalCoroutinesApi
    public val currentTime: Long
        get() = testScheduler.currentTime

    /**
     * Advances the [testScheduler] by [delayTimeMillis].
     *
     * Historical note: this method used to also run the tasks scheduled on the next millisecond after the delay; this
     * behavior is no longer present, so call [runCurrent] afterwards if you need those tasks to run.
     *
     * @see TestCoroutineScheduler.advanceTimeBy
     */
    @ExperimentalCoroutinesApi
    public fun advanceTimeBy(delayTimeMillis: Long): Unit = testScheduler.advanceTimeBy(delayTimeMillis)

    /**
     * Advances the [testScheduler] to the point where there are no tasks remaining.
     * @see TestCoroutineScheduler.advanceUntilIdle
     */
    @ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
    public fun advanceUntilIdle(): Unit = testScheduler.advanceUntilIdle()

    /**
     * Run any tasks that are pending at the current virtual time.
     * @see TestCoroutineScheduler.runCurrent
     */
    @ExperimentalCoroutinesApi
    public fun runCurrent(): Unit = testScheduler.runCurrent()

    @ExperimentalCoroutinesApi
    @Deprecated("The test coroutine scope isn't able to pause its dispatchers in the general case. " +
        "Only `TestCoroutineDispatcher` supports pausing; pause it directly.", level = DeprecationLevel.WARNING)
    public suspend fun pauseDispatcher(block: suspend () -> Unit)

    @ExperimentalCoroutinesApi
    @Deprecated("The test coroutine scope isn't able to pause its dispatchers in the general case. " +
        "Only `TestCoroutineDispatcher` supports pausing; pause it directly.", level = DeprecationLevel.WARNING)
    public fun pauseDispatcher()

    @ExperimentalCoroutinesApi
    @Deprecated("The test coroutine scope isn't able to pause its dispatchers in the general case. " +
        "Only `TestCoroutineDispatcher` supports pausing; pause it directly.", level = DeprecationLevel.WARNING)
    public fun resumeDispatcher()
}

private class TestCoroutineScopeImpl (
    override val coroutineContext: CoroutineContext,
    override val testScheduler: TestCoroutineScheduler
):
    TestCoroutineScope,
    UncaughtExceptionCaptor by coroutineContext.uncaughtExceptionCaptor
{
    override fun cleanupTestCoroutines() {
        coroutineContext.uncaughtExceptionCaptor.cleanupTestCoroutinesCaptor()
        coroutineContext.delayController?.cleanupTestCoroutines()
    }

    @ExperimentalCoroutinesApi
    override suspend fun pauseDispatcher(block: suspend () -> Unit) {
        delayControllerForPausing.pauseDispatcher(block)
    }

    @ExperimentalCoroutinesApi
    override fun pauseDispatcher() {
        delayControllerForPausing.pauseDispatcher()
    }

    @ExperimentalCoroutinesApi
    override fun resumeDispatcher() {
        delayControllerForPausing.resumeDispatcher()
    }

    private val delayControllerForPausing: DelayController
        get() = coroutineContext.delayController
            ?: throw IllegalStateException("This scope isn't able to pause its dispatchers")
}

/**
 * A scope which provides detailed control over the execution of coroutines for tests.
 *
 * If the provided context does not provide a [ContinuationInterceptor] (Dispatcher) or [CoroutineExceptionHandler], the
 * scope adds [TestCoroutineDispatcher] and [TestCoroutineExceptionHandler] automatically.
 *
 * @param context an optional context that MAY provide [UncaughtExceptionCaptor] and/or [DelayController]
 */
@Suppress("FunctionName")
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun TestCoroutineScope(context: CoroutineContext = EmptyCoroutineContext): TestCoroutineScope =
    context.checkTestScopeArguments().let { TestCoroutineScopeImpl(it.first, it.second.scheduler) }

private inline val CoroutineContext.uncaughtExceptionCaptor: UncaughtExceptionCaptor
    get() {
        val handler = this[CoroutineExceptionHandler]
        return handler as? UncaughtExceptionCaptor ?: throw IllegalArgumentException(
            "TestCoroutineScope requires a UncaughtExceptionCaptor such as " +
                "TestCoroutineExceptionHandler as the CoroutineExceptionHandler"
        )
    }

private inline val CoroutineContext.delayController: DelayController?
    get() {
        val handler = this[ContinuationInterceptor]
        return handler as? DelayController
    }