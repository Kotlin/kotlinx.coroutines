/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * A coroutine scope that for launching test coroutines.
 *
 * The scope provides the following functionality:
 * * The [coroutineContext] includes a [coroutine dispatcher][TestDispatcher] that supports delay-skipping, using
 *   a [TestCoroutineScheduler] for orchestrating the virtual time.
 *   This scheduler is also available via the [testScheduler] property, and some helper extension
 *   methods are defined to more conveniently interact with it: see [TestScope.currentTime], [TestScope.runCurrent],
 *   [TestScope.advanceTimeBy], and [TestScope.advanceUntilIdle].
 * * When inside [runTest], uncaught exceptions from the child coroutines of this scope will be reported at the end of
 *   the test.
 *   It is invalid for child coroutines to throw uncaught exceptions when outside the call to [TestScope.runTest]:
 *   the only guarantee in this case is the best effort to deliver the exception.
 *
 * The usual way to access a [TestScope] is to call [runTest], but it can also be constructed manually, in order to
 * use it to initialize the components that participate in the test.
 *
 * #### Differences from the deprecated [TestCoroutineScope]
 *
 * * This doesn't provide an equivalent of [TestCoroutineScope.cleanupTestCoroutines], and so can't be used as a
 *   standalone mechanism for writing tests: it does require that [runTest] is eventually called.
 *   The reason for this is that a proper cleanup procedure that supports using non-test dispatchers and arbitrary
 *   coroutine suspensions would be equivalent to [runTest], but would also be more error-prone, due to the potential
 *   for forgetting to perform the cleanup.
 * * [TestCoroutineScope.advanceTimeBy] also calls [TestCoroutineScheduler.runCurrent] after advancing the virtual time.
 * * No support for dispatcher pausing, like [DelayController] allows. [TestCoroutineDispatcher], which supported
 *   pausing, is deprecated; now, instead of pausing a dispatcher, one can use [withContext] to run a dispatcher that's
 *   paused by default, like [StandardTestDispatcher].
 * * No access to the list of unhandled exceptions.
 */
@ExperimentalCoroutinesApi
public sealed interface TestScope : CoroutineScope {
    /**
     * The delay-skipping scheduler used by the test dispatchers running the code in this scope.
     */
    @ExperimentalCoroutinesApi
    public val testScheduler: TestCoroutineScheduler
}

/**
 * The current virtual time on [testScheduler][TestScope.testScheduler].
 * @see TestCoroutineScheduler.currentTime
 */
@ExperimentalCoroutinesApi
public val TestScope.currentTime: Long
    get() = testScheduler.currentTime

/**
 * Advances the [testScheduler][TestScope.testScheduler] to the point where there are no tasks remaining.
 * @see TestCoroutineScheduler.advanceUntilIdle
 */
@ExperimentalCoroutinesApi
public fun TestScope.advanceUntilIdle(): Unit = testScheduler.advanceUntilIdle()

/**
 * Run any tasks that are pending at the current virtual time, according to
 * the [testScheduler][TestScope.testScheduler].
 *
 * @see TestCoroutineScheduler.runCurrent
 */
@ExperimentalCoroutinesApi
public fun TestScope.runCurrent(): Unit = testScheduler.runCurrent()

/**
 * Moves the virtual clock of this dispatcher forward by [the specified amount][delayTimeMillis], running the
 * scheduled tasks in the meantime.
 *
 * In contrast with [TestScope.advanceTimeBy], this function does not run the tasks scheduled at the moment
 * [currentTime] + [delayTimeMillis].
 *
 * @throws IllegalStateException if passed a negative [delay][delayTimeMillis].
 * @see TestCoroutineScheduler.advanceTimeBy
 */
@ExperimentalCoroutinesApi
public fun TestScope.advanceTimeBy(delayTimeMillis: Long): Unit = testScheduler.advanceTimeBy(delayTimeMillis)

/**
 * Creates a [TestScope].
 *
 * It ensures that all the test module machinery is properly initialized.
 * * If [context] doesn't provide a [TestCoroutineScheduler] for orchestrating the virtual time used for delay-skipping,
 *   a new one is created, unless either
 *   - a [TestDispatcher] is provided, in which case [TestDispatcher.scheduler] is used;
 *   - at the moment of the creation of the scope, [Dispatchers.Main] is delegated to a [TestDispatcher], in which case
 *     its [TestCoroutineScheduler] is used.
 * * If [context] doesn't have a [TestDispatcher], a [StandardTestDispatcher] is created.
 * * A [CoroutineExceptionHandler] is created that makes [TestCoroutineScope.cleanupTestCoroutines] throw if there were
 *   any uncaught exceptions, or forwards the exceptions further in a platform-specific manner if the cleanup was
 *   already performed when an exception happened. Passing a [CoroutineExceptionHandler] is illegal, unless it's an
 *   [UncaughtExceptionCaptor], in which case the behavior is preserved for the time being for backward compatibility.
 *   If you need to have a specific [CoroutineExceptionHandler], please pass it to [launch] on an already-created
 *   [TestCoroutineScope] and share your use case at
 *   [our issue tracker](https://github.com/Kotlin/kotlinx.coroutines/issues).
 * * If [context] provides a [Job], that job is used as a parent for the new scope.
 *
 * @throws IllegalArgumentException if [context] has both [TestCoroutineScheduler] and a [TestDispatcher] linked to a
 * different scheduler.
 * @throws IllegalArgumentException if [context] has a [ContinuationInterceptor] that is not a [TestDispatcher].
 * @throws IllegalArgumentException if [context] has an [CoroutineExceptionHandler] that is not an
 * [UncaughtExceptionCaptor].
 */
@ExperimentalCoroutinesApi
@Suppress("FunctionName")
public fun TestScope(context: CoroutineContext = EmptyCoroutineContext): TestScope {
    val ctxWithDispatcher = context.withDelaySkipping()
    var scope: TestScopeImpl? = null
    val exceptionHandler = when (ctxWithDispatcher[CoroutineExceptionHandler]) {
        null -> CoroutineExceptionHandler { _, exception ->
            scope!!.reportException(exception)
        }
        else -> throw IllegalArgumentException(
            "A CoroutineExceptionHandler was passed to TestScope. " +
                "Please pass it as an argument to a `launch` or `async` block on an already-created scope " +
                "if uncaught exceptions require special treatment."
        )
    }
    return TestScopeImpl(ctxWithDispatcher + exceptionHandler).also { scope = it }
}

/**
 * Adds a [TestDispatcher] and a [TestCoroutineScheduler] to the context if there aren't any already.
 *
 * @throws IllegalArgumentException if both a [TestCoroutineScheduler] and a [TestDispatcher] are passed.
 * @throws IllegalArgumentException if a [ContinuationInterceptor] is passed that is not a [TestDispatcher].
 */
internal fun CoroutineContext.withDelaySkipping(): CoroutineContext {
    val dispatcher: TestDispatcher = when (val dispatcher = get(ContinuationInterceptor)) {
        is TestDispatcher -> {
            val ctxScheduler = get(TestCoroutineScheduler)
            if (ctxScheduler != null) {
                require(dispatcher.scheduler === ctxScheduler) {
                    "Both a TestCoroutineScheduler $ctxScheduler and TestDispatcher $dispatcher linked to " +
                        "another scheduler were passed."
                }
            }
            dispatcher
        }
        null -> StandardTestDispatcher(get(TestCoroutineScheduler))
        else -> throw IllegalArgumentException("Dispatcher must implement TestDispatcher: $dispatcher")
    }
    return this + dispatcher + dispatcher.scheduler
}

internal class TestScopeImpl(context: CoroutineContext) :
    AbstractCoroutine<Unit>(context, initParentJob = true, active = true), TestScope {

    override val testScheduler get() = context[TestCoroutineScheduler]!!

    private var entered = false
    private var finished = false
    private val uncaughtExceptions = mutableListOf<Throwable>()
    private val lock = SynchronizedObject()

    /** Called upon entry to [runTest]. Will throw if called more than once. */
    fun enter() {
        val exceptions = synchronized(lock) {
            if (entered)
                throw IllegalStateException("Only a single call to `runTest` can be performed during one test.")
            entered = true
            check(!finished)
            uncaughtExceptions
        }
        if (exceptions.isNotEmpty()) {
            throw UncaughtExceptionsBeforeTest().apply {
                for (e in exceptions)
                    addSuppressed(e)
            }
        }
    }

    /** Called at the end of the test. May only be called once. */
    fun leave(): List<Throwable> {
        val exceptions = synchronized(lock) {
            if(!entered || finished)
                throw IllegalStateException("An internal error. Please report to the Kotlinx Coroutines issue tracker")
            finished = true
            uncaughtExceptions
        }
        val activeJobs = children.filter { it.isActive }.toList() // only non-empty if used with `runBlockingTest`
        if (exceptions.isEmpty()) {
            if (activeJobs.isNotEmpty())
                throw UncompletedCoroutinesError(
                    "Active jobs found during the tear-down. " +
                        "Ensure that all coroutines are completed or cancelled by your test. " +
                        "The active jobs: $activeJobs"
                )
            if (!testScheduler.isIdle())
                throw UncompletedCoroutinesError(
                    "Unfinished coroutines found during the tear-down. " +
                        "Ensure that all coroutines are completed or cancelled by your test."
                )
        }
        return exceptions
    }

    /** Stores an exception to report after [runTest], or rethrows it if not inside [runTest]. */
    fun reportException(throwable: Throwable) {
        synchronized(lock) {
            if (finished) {
                throw throwable
            } else {
                uncaughtExceptions.add(throwable)
                if (!entered)
                    throw UncaughtExceptionsBeforeTest().apply { addSuppressed(throwable) }
            }
        }
    }

    /** Throws an exception if the coroutine is not completing. */
    fun tryGetCompletionCause(): Throwable? = completionCause

    override fun toString(): String =
        "TestScope[" + (if (finished) "test ended" else if (entered) "test started" else "test not started") + "]"
}

/** Use the knowledge that any [TestScope] that we receive is necessarily a [TestScopeImpl]. */
internal fun TestScope.asSpecificImplementation(): TestScopeImpl = when (this) {
    is TestScopeImpl -> this
}

internal class UncaughtExceptionsBeforeTest : IllegalStateException(
    "There were uncaught exceptions in coroutines launched from TestScope before the test started. Please avoid this," +
        " as such exceptions are also reported in a platform-dependent manner so that they are not lost."
)

/**
 * Thrown when a test has completed and there are tasks that are not completed or cancelled.
 */
@ExperimentalCoroutinesApi
internal class UncompletedCoroutinesError(message: String) : AssertionError(message)