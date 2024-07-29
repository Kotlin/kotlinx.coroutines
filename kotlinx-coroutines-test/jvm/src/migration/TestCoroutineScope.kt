@file:Suppress("DEPRECATION_ERROR", "DEPRECATION")

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * @suppress
 */
@ExperimentalCoroutinesApi
@Deprecated("Use `TestScope` in combination with `runTest` instead." +
    "Please see the migration guide for details: " +
    "https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-test/MIGRATION.md",
    level = DeprecationLevel.ERROR)
// Since 1.6.0, kept as warning in 1.7.0, ERROR in 1.9.0 and removed as experimental later
public interface TestCoroutineScope : CoroutineScope {
    /**
     * @suppress
     */
    @ExperimentalCoroutinesApi
    @Deprecated(
        "Please call `runTest`, which automatically performs the cleanup, instead of using this function.",
        level = DeprecationLevel.ERROR
    )
    // Since 1.6.0, kept as warning in 1.7.0, ERROR in 1.9.0 and removed as experimental later
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

    @Deprecated("Please call `runTest`, which automatically performs the cleanup, instead of using this function.")
    override fun cleanupTestCoroutines() {
        val delayController = coroutineContext.delayController
        val hasUnfinishedJobs = if (delayController != null) {
            try {
                delayController.cleanupTestCoroutines()
                false
            } catch (_: UncompletedCoroutinesError) {
                true
            }
        } else {
            testScheduler.runCurrent()
            !testScheduler.isIdle(strict = false)
        }
        (coroutineContext[CoroutineExceptionHandler] as? TestCoroutineExceptionHandler)?.cleanupTestCoroutines()
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
 * @suppress
 */
@Deprecated(
    "This constructs a `TestCoroutineScope` with a deprecated `CoroutineDispatcher` by default. " +
        "Please use `createTestCoroutineScope` instead.",
    ReplaceWith(
        "createTestCoroutineScope(TestCoroutineDispatcher() + TestCoroutineExceptionHandler() + context)",
        "kotlin.coroutines.EmptyCoroutineContext"
    ),
    level = DeprecationLevel.ERROR
)
// Since 1.6.0, kept as warning in 1.7.0, ERROR in 1.9.0 and removed as experimental later
public fun TestCoroutineScope(context: CoroutineContext = EmptyCoroutineContext): TestCoroutineScope {
    val scheduler = context[TestCoroutineScheduler] ?: TestCoroutineScheduler()
    return createTestCoroutineScope(TestCoroutineDispatcher(scheduler) + TestCoroutineExceptionHandler() + context)
}

/**
 * @suppress
 */
@ExperimentalCoroutinesApi
@Deprecated(
    "This function was introduced in order to help migrate from TestCoroutineScope to TestScope. " +
        "Please use TestScope() construction instead, or just runTest(), without creating a scope.",
    level = DeprecationLevel.ERROR
)
// Since 1.6.0, kept as warning in 1.7.0, ERROR in 1.9.0 and removed as experimental later
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
        is TestCoroutineExceptionHandler -> exceptionHandler
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

private inline val CoroutineContext.delayController: TestCoroutineDispatcher?
    get() {
        val handler = this[ContinuationInterceptor]
        return handler as? TestCoroutineDispatcher
    }


/**
 * The current virtual time on [testScheduler][TestCoroutineScope.testScheduler].
 * @see TestCoroutineScheduler.currentTime
 */
@ExperimentalCoroutinesApi
public val TestCoroutineScope.currentTime: Long
    get() = coroutineContext.delayController?.currentTime ?: testScheduler.currentTime

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
