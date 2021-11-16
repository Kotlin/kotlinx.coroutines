/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("DEPRECATION")

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * A scope which provides detailed control over the execution of coroutines for tests.
 */
@ExperimentalCoroutinesApi
@Deprecated("Use `TestScope` in combination with `runTest` instead")
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public sealed interface TestCoroutineScope : CoroutineScope {
    /**
     * Called after the test completes.
     *
     * * It checks that there were no uncaught exceptions caught by its [CoroutineExceptionHandler].
     *   If there were any, then the first one is thrown, whereas the rest are suppressed by it.
     * * It runs the tasks pending in the scheduler at the current time. If there are any uncompleted tasks afterwards,
     *   it fails with [UncompletedCoroutinesError].
     * * It checks whether some new child [Job]s were created but not completed since this [TestCoroutineScope] was
     *   created. If so, it fails with [UncompletedCoroutinesError].
     *
     * For backward compatibility, if the [CoroutineExceptionHandler] is an [UncaughtExceptionCaptor], its
     * [TestCoroutineExceptionHandler.cleanupTestCoroutines] behavior is performed.
     * Likewise, if the [ContinuationInterceptor] is a [DelayController], its [DelayController.cleanupTestCoroutines]
     * is called.
     *
     * @throws Throwable the first uncaught exception, if there are any uncaught exceptions.
     * @throws AssertionError if any pending tasks are active.
     * @throws IllegalStateException if called more than once.
     */
    @ExperimentalCoroutinesApi
    @Deprecated("Please call `runTest`, which automatically performs the cleanup, instead of using this function.")
    // Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
    public fun cleanupTestCoroutines()

    /**
     * The delay-skipping scheduler used by the test dispatchers running the code in this scope.
     */
    @ExperimentalCoroutinesApi
    public val testScheduler: TestCoroutineScheduler
}

private class TestCoroutineScopeImpl(
    override val coroutineContext: CoroutineContext
) : TestCoroutineScope {
    private val lock = SynchronizedObject()
    private var exceptions = mutableListOf<Throwable>()
    private var cleanedUp = false

    /**
     * Reports an exception so that it is thrown on [cleanupTestCoroutines].
     *
     * If several exceptions are reported, only the first one will be thrown, and the other ones will be suppressed by
     * it.
     *
     * Returns `false` if [cleanupTestCoroutines] was already called.
     */
    fun reportException(throwable: Throwable): Boolean =
        synchronized(lock) {
            if (cleanedUp) {
                false
            } else {
                exceptions.add(throwable)
                true
            }
        }

    override val testScheduler: TestCoroutineScheduler
        get() = coroutineContext[TestCoroutineScheduler]!!

    /** These jobs existed before the coroutine scope was used, so it's alright if they don't get cancelled. */
    private val initialJobs = coroutineContext.activeJobs()

    override fun cleanupTestCoroutines() {
        val delayController = coroutineContext.delayController
        val hasUnfinishedJobs = if (delayController != null) {
            try {
                delayController.cleanupTestCoroutines()
                false
            } catch (e: UncompletedCoroutinesError) {
                true
            }
        } else {
            testScheduler.runCurrent()
            !testScheduler.isIdle(strict = false)
        }
        (coroutineContext[CoroutineExceptionHandler] as? UncaughtExceptionCaptor)?.cleanupTestCoroutines()
        synchronized(lock) {
            if (cleanedUp)
                throw IllegalStateException("Attempting to clean up a test coroutine scope more than once.")
            cleanedUp = true
        }
        exceptions.firstOrNull()?.let { toThrow ->
            exceptions.drop(1).forEach { toThrow.addSuppressed(it) }
            throw toThrow
        }
        if (hasUnfinishedJobs)
            throw UncompletedCoroutinesError(
                "Unfinished coroutines during teardown. Ensure all coroutines are" +
                    " completed or cancelled by your test."
            )
        val jobs = coroutineContext.activeJobs()
        if ((jobs - initialJobs).isNotEmpty())
            throw UncompletedCoroutinesError("Test finished with active jobs: $jobs")
    }
}

internal fun CoroutineContext.activeJobs(): Set<Job> {
    return checkNotNull(this[Job]).children.filter { it.isActive }.toSet()
}

/**
 * A coroutine scope for launching test coroutines using [TestCoroutineDispatcher].
 *
 * [createTestCoroutineScope] is a similar function that defaults to [StandardTestDispatcher].
 */
@Deprecated(
    "This constructs a `TestCoroutineScope` with a deprecated `CoroutineDispatcher` by default. " +
        "Please use `createTestCoroutineScope` instead.",
    ReplaceWith(
        "createTestCoroutineScope(TestCoroutineDispatcher() + TestCoroutineExceptionHandler() + context)",
        "kotlin.coroutines.EmptyCoroutineContext"
    ),
    level = DeprecationLevel.WARNING
)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public fun TestCoroutineScope(context: CoroutineContext = EmptyCoroutineContext): TestCoroutineScope {
    val scheduler = context[TestCoroutineScheduler] ?: TestCoroutineScheduler()
    return createTestCoroutineScope(TestCoroutineDispatcher(scheduler) + TestCoroutineExceptionHandler() + context)
}

/**
 * A coroutine scope for launching test coroutines.
 *
 * It ensures that all the test module machinery is properly initialized.
 * * If [context] doesn't define a [TestCoroutineScheduler] for orchestrating the virtual time used for delay-skipping,
 *   a new one is created, unless either
 *   - a [TestDispatcher] is provided, in which case [TestDispatcher.scheduler] is used;
 *   - at the moment of the creation of the scope, [Dispatchers.Main] is delegated to a [TestDispatcher], in which case
 *     its [TestCoroutineScheduler] is used.
 * * If [context] doesn't have a [ContinuationInterceptor], a [StandardTestDispatcher] is created.
 * * A [CoroutineExceptionHandler] is created that makes [TestCoroutineScope.cleanupTestCoroutines] throw if there were
 *   any uncaught exceptions, or forwards the exceptions further in a platform-specific manner if the cleanup was
 *   already performed when an exception happened. Passing a [CoroutineExceptionHandler] is illegal, unless it's an
 *   [UncaughtExceptionCaptor], in which case the behavior is preserved for the time being for backward compatibility.
 *   If you need to have a specific [CoroutineExceptionHandler], please pass it to [launch] on an already-created
 *   [TestCoroutineScope] and share your use case at
 *   [our issue tracker](https://github.com/Kotlin/kotlinx.coroutines/issues).
 * * If [context] provides a [Job], that job is used for the new scope; otherwise, a [CompletableJob] is created.
 *
 * @throws IllegalArgumentException if [context] has both [TestCoroutineScheduler] and a [TestDispatcher] linked to a
 * different scheduler.
 * @throws IllegalArgumentException if [context] has a [ContinuationInterceptor] that is not a [TestDispatcher].
 * @throws IllegalArgumentException if [context] has an [CoroutineExceptionHandler] that is not an
 * [UncaughtExceptionCaptor].
 */
@ExperimentalCoroutinesApi
@Deprecated(
    "This function was introduced in order to help migrate from TestCoroutineScope to TestScope. " +
        "Please use TestScope() construction instead, or just runTest(), without creating a scope.",
    level = DeprecationLevel.WARNING
)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public fun createTestCoroutineScope(context: CoroutineContext = EmptyCoroutineContext): TestCoroutineScope {
    val ctxWithDispatcher = context.withDelaySkipping()
    var scope: TestCoroutineScopeImpl? = null
    val ownExceptionHandler =
        object : AbstractCoroutineContextElement(CoroutineExceptionHandler), TestCoroutineScopeExceptionHandler {
            override fun handleException(context: CoroutineContext, exception: Throwable) {
                if (!scope!!.reportException(exception))
                    throw exception // let this exception crash everything
            }
        }
    val exceptionHandler = when (val exceptionHandler = ctxWithDispatcher[CoroutineExceptionHandler]) {
        is UncaughtExceptionCaptor -> exceptionHandler
        null -> ownExceptionHandler
        is TestCoroutineScopeExceptionHandler -> ownExceptionHandler
        else -> throw IllegalArgumentException(
            "A CoroutineExceptionHandler was passed to TestCoroutineScope. " +
                "Please pass it as an argument to a `launch` or `async` block on an already-created scope " +
                "if uncaught exceptions require special treatment."
        )
    }
    val job: Job = ctxWithDispatcher[Job] ?: Job()
    return TestCoroutineScopeImpl(ctxWithDispatcher + exceptionHandler + job).also {
        scope = it
    }
}

/** A marker that shows that this [CoroutineExceptionHandler] was created for [TestCoroutineScope]. With this,
 * constructing a new [TestCoroutineScope] with the [CoroutineScope.coroutineContext] of an existing one will override
 * the exception handler, instead of failing. */
private interface TestCoroutineScopeExceptionHandler : CoroutineExceptionHandler

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
@Deprecated(
    "The name of this function is misleading: it not only advances the time, but also runs the tasks " +
        "scheduled *at* the ending moment.",
    ReplaceWith("this.testScheduler.apply { advanceTimeBy(delayTimeMillis); runCurrent() }"),
    DeprecationLevel.WARNING
)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
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
@Deprecated(
    "The test coroutine scope isn't able to pause its dispatchers in the general case. " +
        "Only `TestCoroutineDispatcher` supports pausing; pause it directly, or use a dispatcher that is always " +
        "\"paused\", like `StandardTestDispatcher`.",
    ReplaceWith(
        "(this.coroutineContext[ContinuationInterceptor]!! as DelayController).pauseDispatcher(block)",
        "kotlin.coroutines.ContinuationInterceptor"
    ),
    DeprecationLevel.WARNING
)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public suspend fun TestCoroutineScope.pauseDispatcher(block: suspend () -> Unit) {
    delayControllerForPausing.pauseDispatcher(block)
}

@ExperimentalCoroutinesApi
@Deprecated(
    "The test coroutine scope isn't able to pause its dispatchers in the general case. " +
        "Only `TestCoroutineDispatcher` supports pausing; pause it directly, or use a dispatcher that is always " +
        "\"paused\", like `StandardTestDispatcher`.",
    ReplaceWith(
        "(this.coroutineContext[ContinuationInterceptor]!! as DelayController).pauseDispatcher()",
        "kotlin.coroutines.ContinuationInterceptor"
    ),
    level = DeprecationLevel.WARNING
)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public fun TestCoroutineScope.pauseDispatcher() {
    delayControllerForPausing.pauseDispatcher()
}

@ExperimentalCoroutinesApi
@Deprecated(
    "The test coroutine scope isn't able to pause its dispatchers in the general case. " +
        "Only `TestCoroutineDispatcher` supports pausing; pause it directly, or use a dispatcher that is always " +
        "\"paused\", like `StandardTestDispatcher`.",
    ReplaceWith(
        "(this.coroutineContext[ContinuationInterceptor]!! as DelayController).resumeDispatcher()",
        "kotlin.coroutines.ContinuationInterceptor"
    ),
    level = DeprecationLevel.WARNING
)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
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
    level = DeprecationLevel.WARNING
)
public val TestCoroutineScope.uncaughtExceptions: List<Throwable>
    get() = (coroutineContext[CoroutineExceptionHandler] as? UncaughtExceptionCaptor)?.uncaughtExceptions
        ?: emptyList()

private val TestCoroutineScope.delayControllerForPausing: DelayController
    get() = coroutineContext.delayController
        ?: throw IllegalStateException("This scope isn't able to pause its dispatchers")
