/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * A scope which provides detailed control over the execution of coroutines for tests.
 */
@ExperimentalCoroutinesApi
public interface TestCoroutineScope: CoroutineScope {
    /**
     * Called after the test completes.
     *
     * * It checks that there were no uncaught exceptions reported via [reportException]. If there were any, then the
     *   first one is thrown, whereas the rest are printed to the standard output or the standard error output
     *   (see [Throwable.printStackTrace]).
     * * It runs the tasks pending in the scheduler at the current time. If there are any uncompleted tasks afterwards,
     *   it fails with [UncompletedCoroutinesError].
     * * It checks whether some new child [Job]s were created but not completed since this [TestCoroutineScope] was
     *   created. If so, it fails with [UncompletedCoroutinesError].
     *
     * For backwards compatibility, if the [CoroutineExceptionHandler] is an [UncaughtExceptionCaptor], its
     * [TestCoroutineExceptionHandler.cleanupTestCoroutines] behavior is performed.
     * Likewise, if the [ContinuationInterceptor] is a [DelayController], its [DelayController.cleanupTestCoroutines]
     * is called.
     *
     * @throws Throwable the first uncaught exception, if there are any uncaught exceptions.
     * @throws UncompletedCoroutinesError if any pending tasks are active.
     * @throws IllegalStateException if called more than once.
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

    /**
     * Reports an exception so that it is thrown on [cleanupTestCoroutines].
     *
     * If several exceptions are reported, only the first one will be thrown, and the other ones will be printed to the
     * console.
     *
     * @throws IllegalStateException with the [Throwable.cause] set to [throwable] if [cleanupTestCoroutines] was
     * already called.
     */
    @ExperimentalCoroutinesApi
    public fun reportException(throwable: Throwable)
}

private class TestCoroutineScopeImpl (
    override val coroutineContext: CoroutineContext,
    val ownJob: CompletableJob?
): TestCoroutineScope
{
    private val lock = SynchronizedObject()
    private var exceptions = mutableListOf<Throwable>()
    private var cleanedUp = false

    override fun reportException(throwable: Throwable) {
        synchronized(lock) {
            if (cleanedUp)
                throw IllegalStateException(
                    "Attempting to report an uncaught exception after the test coroutine scope was already cleaned up",
                    throwable)
            exceptions.add(throwable)
        }
    }

    override val testScheduler: TestCoroutineScheduler
        get() = coroutineContext[TestCoroutineScheduler]!!

    /** These jobs existed before the coroutine scope was used, so it's alright if they don't get cancelled. */
    val initialJobs = coroutineContext.activeJobs()

    override fun cleanupTestCoroutines() {
        synchronized(lock) {
            if (cleanedUp)
                throw IllegalStateException("Attempting to clean up a test coroutine scope more than once.")
            cleanedUp = true
        }
        exceptions.apply {
            drop(1).forEach { it.printStackTrace() }
            singleOrNull()?.let { throw it }
        }
        (coroutineContext[CoroutineExceptionHandler] as? UncaughtExceptionCaptor)?.cleanupTestCoroutines()
        val delayController = coroutineContext.delayController
        if (delayController != null) {
            delayController.cleanupTestCoroutines()
        } else {
            testScheduler.runCurrent()
            if (!testScheduler.isIdle()) {
                throw UncompletedCoroutinesError(
                    "Unfinished coroutines during teardown. Ensure all coroutines are" +
                        " completed or cancelled by your test."
                )
            }
        }
        val jobs = coroutineContext.activeJobs()
        if ((jobs - initialJobs).isNotEmpty()) {
            throw UncompletedCoroutinesError("Test finished with active jobs: $jobs")
        }
        ownJob?.complete()
    }
}

private fun CoroutineContext.activeJobs(): Set<Job> {
    return checkNotNull(this[Job]).children.filter { it.isActive }.toSet()
}

/**
 * A coroutine scope for launching test coroutines using [TestCoroutineDispatcher].
 *
 * [createTestCoroutineScope] is a similar function that defaults to [StandardTestDispatcher].
 */
@Deprecated("This constructs a `TestCoroutineScope` with a deprecated `CoroutineDispatcher` by default. " +
    "Please use `createTestCoroutineScope` instead.",
    ReplaceWith("createTestCoroutineScope(TestCoroutineDispatcher() + TestCoroutineExceptionHandler() + context)",
        "kotlin.coroutines.EmptyCoroutineContext"),
    level = DeprecationLevel.WARNING
)
public fun TestCoroutineScope(context: CoroutineContext = EmptyCoroutineContext): TestCoroutineScope {
    val scheduler = context[TestCoroutineScheduler] ?: TestCoroutineScheduler()
    return createTestCoroutineScope(TestCoroutineDispatcher(scheduler) + TestCoroutineExceptionHandler() + context)
}

/**
 * A coroutine scope for launching test coroutines.
 *
 * It ensures that all the test module machinery is properly initialized.
 * * If [context] doesn't define a [TestCoroutineScheduler] for orchestrating the virtual time used for delay-skipping,
 *   a new one is created, unless a [TestDispatcher] is provided, in which case [TestDispatcher.scheduler] is used.
 * * If [context] doesn't have a [ContinuationInterceptor], a [StandardTestDispatcher] is created.
 * * If [context] does not provide a [CoroutineExceptionHandler], [TestCoroutineExceptionHandler] is created
 *   automatically.
 * * If [context] provides a [Job], that job is used for the new scope, but is not completed once the scope completes.
 *   On the other hand, if there is no [Job] in the context, a [CompletableJob] is created and completed on
 *   [TestCoroutineScope.cleanupTestCoroutines].
 *
 * @throws IllegalArgumentException if [context] has both [TestCoroutineScheduler] and a [TestDispatcher] linked to a
 * different scheduler.
 * @throws IllegalArgumentException if [context] has a [ContinuationInterceptor] that is not a [TestDispatcher].
 * @throws IllegalArgumentException if [context] has an [CoroutineExceptionHandler] that is not an
 * [UncaughtExceptionCaptor].
 */
@ExperimentalCoroutinesApi
public fun createTestCoroutineScope(context: CoroutineContext = EmptyCoroutineContext): TestCoroutineScope {
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
            StandardTestDispatcher(scheduler)
        }
        else -> throw IllegalArgumentException("Dispatcher must implement TestDispatcher: $dispatcher")
    }
    val exceptionHandler = context[CoroutineExceptionHandler]
        ?: TestExceptionHandler { _, throwable -> reportException(throwable) }
    val job: Job
    val ownJob: CompletableJob?
    if (context[Job] == null) {
        ownJob = SupervisorJob()
        job = ownJob
    } else {
        ownJob = null
        job = context[Job]!!
    }
    return TestCoroutineScopeImpl(context + scheduler + dispatcher + exceptionHandler + job, ownJob)
        .also { (exceptionHandler as? TestExceptionHandlerContextElement)?.tryRegisterTestCoroutineScope(it) }
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
public fun TestCoroutineScope.advanceUntilIdle() {
    coroutineContext.delayController?.advanceUntilIdle() ?: testScheduler.advanceUntilIdle()
}

/**
 * Run any tasks that are pending at the current virtual time, according to
 * the [testScheduler][TestCoroutineScope.testScheduler].
 *
 * @see TestCoroutineScheduler.runCurrent
 */
@ExperimentalCoroutinesApi
public fun TestCoroutineScope.runCurrent() {
    coroutineContext.delayController?.runCurrent() ?: testScheduler.runCurrent()
}

@ExperimentalCoroutinesApi
@Deprecated("The test coroutine scope isn't able to pause its dispatchers in the general case. " +
    "Only `TestCoroutineDispatcher` supports pausing; pause it directly, or use a dispatcher that is always " +
    "\"paused\", like `StandardTestDispatcher`.",
    ReplaceWith("(this.coroutineContext[ContinuationInterceptor]!! as DelayController).pauseDispatcher(block)",
        "kotlin.coroutines.ContinuationInterceptor"),
    DeprecationLevel.WARNING)
public suspend fun TestCoroutineScope.pauseDispatcher(block: suspend () -> Unit) {
    delayControllerForPausing.pauseDispatcher(block)
}

@ExperimentalCoroutinesApi
@Deprecated("The test coroutine scope isn't able to pause its dispatchers in the general case. " +
    "Only `TestCoroutineDispatcher` supports pausing; pause it directly, or use a dispatcher that is always " +
        "\"paused\", like `StandardTestDispatcher`.",
    ReplaceWith("(this.coroutineContext[ContinuationInterceptor]!! as DelayController).pauseDispatcher()",
        "kotlin.coroutines.ContinuationInterceptor"),
level = DeprecationLevel.WARNING)
public fun TestCoroutineScope.pauseDispatcher() {
    delayControllerForPausing.pauseDispatcher()
}

@ExperimentalCoroutinesApi
@Deprecated("The test coroutine scope isn't able to pause its dispatchers in the general case. " +
    "Only `TestCoroutineDispatcher` supports pausing; pause it directly, or use a dispatcher that is always " +
        "\"paused\", like `StandardTestDispatcher`.",
    ReplaceWith("(this.coroutineContext[ContinuationInterceptor]!! as DelayController).resumeDispatcher()",
        "kotlin.coroutines.ContinuationInterceptor"),
    level = DeprecationLevel.WARNING)
public fun TestCoroutineScope.resumeDispatcher() {
    delayControllerForPausing.resumeDispatcher()
}

/**
 * List of uncaught coroutine exceptions, for backward compatibility.
 *
 * The returned list is a copy of the exceptions caught during execution.
 * During [TestCoroutineScope.cleanupTestCoroutines] the first element of this list is rethrown if it is not empty.
 *
 * Exceptions are only collected in this list if the [UncaughtExceptionCaptor] is in the test context.
 */
@Deprecated(
    "This list is only populated if `UncaughtExceptionCaptor` is in the test context, and so can be " +
        "easily misused. It is only present for backward compatibility and will be removed in the subsequent " +
        "releases. If you need to check the list of exceptions, please consider creating your own " +
        "`CoroutineExceptionHandler`.",
    level = DeprecationLevel.WARNING)
public val TestCoroutineScope.uncaughtExceptions: List<Throwable>
    get() = (coroutineContext[CoroutineExceptionHandler] as? UncaughtExceptionCaptor)?.uncaughtExceptions
        ?: emptyList()

private val TestCoroutineScope.delayControllerForPausing: DelayController
    get() = coroutineContext.delayController
        ?: throw IllegalStateException("This scope isn't able to pause its dispatchers")
