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
    @ExperimentalCoroutinesApi
    public fun cleanupTestCoroutines()

    /**
     * The delay-skipping scheduler used by the test dispatchers running the code in this scope.
     */
    @ExperimentalCoroutinesApi
    public val testScheduler: TestCoroutineScheduler
        get() = coroutineContext[TestCoroutineScheduler]
            ?: throw UnsupportedOperationException("This scope does not have a TestCoroutineScheduler linked to it")
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


/**
 * The current virtual time on [testScheduler][TestCoroutineScope.testScheduler].
 * @see TestCoroutineScheduler.currentTime
 */
@ExperimentalCoroutinesApi
public val TestCoroutineScope.currentTime: Long
    get() = coroutineContext.delayController?.currentTime ?: testScheduler.currentTime

/**
 * Advances the [testScheduler][TestCoroutineScope.testScheduler] by [delayTimeMillis] and runs the tasks up to that
 * moment (inclusive).
 *
 * @see TestCoroutineScheduler.advanceTimeBy
 */
@ExperimentalCoroutinesApi
@Deprecated("The name of this function is misleading: it not only advances the time, but also runs the tasks " +
    "scheduled *at* the ending moment.",
    ReplaceWith("this.testScheduler.apply { advanceTimeBy(delayTimeMillis); runCurrent() }"),
    DeprecationLevel.WARNING)
public fun TestCoroutineScope.advanceTimeBy(delayTimeMillis: Long): Unit =
    when (val controller = coroutineContext.delayController) {
        null -> {
            testScheduler.advanceTimeBy(delayTimeMillis)
            testScheduler.runCurrent()
        }
        else -> {
            controller.advanceTimeBy(delayTimeMillis)
            Unit
        }
    }

/**
 * Advances the [testScheduler][TestCoroutineScope.testScheduler] to the point where there are no tasks remaining.
 * @see TestCoroutineScheduler.advanceUntilIdle
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun TestCoroutineScope.advanceUntilIdle(): Unit {
    coroutineContext.delayController?.advanceUntilIdle() ?: testScheduler.advanceUntilIdle()
}

/**
 * Run any tasks that are pending at the current virtual time, according to
 * the [testScheduler][TestCoroutineScope.testScheduler].
 *
 * @see TestCoroutineScheduler.runCurrent
 */
@ExperimentalCoroutinesApi
public fun TestCoroutineScope.runCurrent(): Unit {
    coroutineContext.delayController?.runCurrent() ?: testScheduler.runCurrent()
}

@ExperimentalCoroutinesApi
@Deprecated("The test coroutine scope isn't able to pause its dispatchers in the general case. " +
    "Only `TestCoroutineDispatcher` supports pausing; pause it directly.",
    ReplaceWith("(this.coroutineContext[ContinuationInterceptor]!! as DelayController).pauseDispatcher(block)",
        "kotlin.coroutines.ContinuationInterceptor"),
    DeprecationLevel.WARNING)
public suspend fun TestCoroutineScope.pauseDispatcher(block: suspend () -> Unit) {
    delayControllerForPausing.pauseDispatcher(block)
}

@ExperimentalCoroutinesApi
@Deprecated("The test coroutine scope isn't able to pause its dispatchers in the general case. " +
    "Only `TestCoroutineDispatcher` supports pausing; pause it directly.",
    ReplaceWith("(this.coroutineContext[ContinuationInterceptor]!! as DelayController).pauseDispatcher()",
        "kotlin.coroutines.ContinuationInterceptor"),
level = DeprecationLevel.WARNING)
public fun TestCoroutineScope.pauseDispatcher() {
    delayControllerForPausing.pauseDispatcher()
}

@ExperimentalCoroutinesApi
@Deprecated("The test coroutine scope isn't able to pause its dispatchers in the general case. " +
    "Only `TestCoroutineDispatcher` supports pausing; pause it directly.",
    ReplaceWith("(this.coroutineContext[ContinuationInterceptor]!! as DelayController).resumeDispatcher()",
        "kotlin.coroutines.ContinuationInterceptor"),
    level = DeprecationLevel.WARNING)
public fun TestCoroutineScope.resumeDispatcher() {
    delayControllerForPausing.resumeDispatcher()
}

private val TestCoroutineScope.delayControllerForPausing: DelayController
    get() = coroutineContext.delayController
        ?: throw IllegalStateException("This scope isn't able to pause its dispatchers")