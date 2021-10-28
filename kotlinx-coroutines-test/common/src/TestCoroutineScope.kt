/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * A scope which provides detailed control over the execution of coroutines for tests.
 */
@ExperimentalCoroutinesApi
public sealed interface TestCoroutineScope: CoroutineScope, UncaughtExceptionCaptor {
    /**
     * Called after the test completes.
     *
     * Calls [UncaughtExceptionCaptor.cleanupTestCoroutinesCaptor] and [DelayController.cleanupTestCoroutines].
     *
     * @throws Throwable the first uncaught exception, if there are any uncaught exceptions.
     * @throws AssertionError if any pending tasks are active.
     */
    @ExperimentalCoroutinesApi
    public fun cleanupTestCoroutines()

    /**
     * The delay-skipping scheduler used by the test dispatchers running the code in this scope.
     */
    @ExperimentalCoroutinesApi
    public val testScheduler: TestCoroutineScheduler
}

private class TestCoroutineScopeImpl(
    override val coroutineContext: CoroutineContext
):
    TestCoroutineScope,
    UncaughtExceptionCaptor by coroutineContext.uncaughtExceptionCaptor
{
    override val testScheduler: TestCoroutineScheduler
        get() = coroutineContext[TestCoroutineScheduler]!!

    /** These jobs existed before the coroutine scope was used, so it's alright if they don't get cancelled. */
    private val initialJobs = coroutineContext.activeJobs()

    override fun cleanupTestCoroutines() {
        coroutineContext.uncaughtExceptionCaptor.cleanupTestCoroutinesCaptor()
        coroutineContext.delayController?.cleanupTestCoroutines()
        val jobs = coroutineContext.activeJobs()
        if ((jobs - initialJobs).isNotEmpty())
            throw UncompletedCoroutinesError("Test finished with active jobs: $jobs")
    }
}

private fun CoroutineContext.activeJobs(): Set<Job> {
    return checkNotNull(this[Job]).children.filter { it.isActive }.toSet()
}

/**
 * A coroutine scope for launching test coroutines.
 *
 * It ensures that all the test module machinery is properly initialized.
 * * If [context] doesn't define a [TestCoroutineScheduler] for orchestrating the virtual time used for delay-skipping,
 *   a new one is created, unless a [TestDispatcher] is provided, in which case [TestDispatcher.scheduler] is used.
 * * If [context] doesn't have a [ContinuationInterceptor], a [TestCoroutineDispatcher] is created.
 * * If [context] does not provide a [CoroutineExceptionHandler], [TestCoroutineExceptionHandler] is created
 *   automatically.
 * * If [context] provides a [Job], that job is used for the new scope; otherwise, a [CompletableJob] is created.
 *
 * @throws IllegalArgumentException if [context] has both [TestCoroutineScheduler] and a [TestDispatcher] linked to a
 * different scheduler.
 * @throws IllegalArgumentException if [context] has a [ContinuationInterceptor] that is not a [TestDispatcher].
 * @throws IllegalArgumentException if [context] has an [CoroutineExceptionHandler] that is not an
 * [UncaughtExceptionCaptor].
 */
@Suppress("FunctionName")
@ExperimentalCoroutinesApi
public fun TestCoroutineScope(context: CoroutineContext = EmptyCoroutineContext): TestCoroutineScope {
    val scheduler: TestCoroutineScheduler
    val dispatcher = when (val dispatcher = context[ContinuationInterceptor]) {
        is TestDispatcher -> {
            scheduler = dispatcher.scheduler
            val ctxScheduler = context[TestCoroutineScheduler]
            if (ctxScheduler != null) {
                require(dispatcher.scheduler === ctxScheduler) {
                    "Both a TestCoroutineScheduler $ctxScheduler and TestDispatcher $dispatcher linked to " +
                        "another scheduler were passed."
                }
            }
            dispatcher
        }
        null -> {
            scheduler = context[TestCoroutineScheduler] ?: TestCoroutineScheduler()
            TestCoroutineDispatcher(scheduler)
        }
        else -> throw IllegalArgumentException("Dispatcher must implement TestDispatcher: $dispatcher")
    }
    val exceptionHandler = context[CoroutineExceptionHandler].run {
        this?.let {
            require(this is UncaughtExceptionCaptor) {
                "coroutineExceptionHandler must implement UncaughtExceptionCaptor: $context"
            }
        }
        this ?: TestCoroutineExceptionHandler()
    }
    val job: Job = context[Job] ?: SupervisorJob()
    return TestCoroutineScopeImpl(context + scheduler + dispatcher + exceptionHandler + job)
}

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
@ExperimentalCoroutinesApi
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

/**
 * Thrown when a test has completed and there are tasks that are not completed or cancelled.
 */
@ExperimentalCoroutinesApi
internal class UncompletedCoroutinesError(message: String): AssertionError(message)
