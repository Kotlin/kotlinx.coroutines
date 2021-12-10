/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("TestBuildersKt")
@file:JvmMultifileClass

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * A test result.
 *
 * * On JVM and Native, this resolves to [Unit], representing the fact that tests are run in a blocking manner on these
 *   platforms: a call to a function returning a [TestResult] will simply execute the test inside it.
 * * On JS, this is a `Promise`, which reflects the fact that the test-running function does not wait for a test to
 *   finish. The JS test frameworks typically support returning `Promise` from a test and will correctly handle it.
 *
 * Because of the behavior on JS, extra care must be taken when writing multiplatform tests to avoid losing test errors:
 * * Don't do anything after running the functions returning a [TestResult]. On JS, this code will execute *before* the
 *   test finishes.
 * * As a corollary, don't run functions returning a [TestResult] more than once per test. The only valid thing to do
 *   with a [TestResult] is to immediately `return` it from a test.
 * * Don't nest functions returning a [TestResult].
 */
@Suppress("NO_ACTUAL_FOR_EXPECT")
@ExperimentalCoroutinesApi
public expect class TestResult

/**
 * Executes [testBody] as a test in a new coroutine, returning [TestResult].
 *
 * On JVM and Native, this function behaves similarly to `runBlocking`, with the difference that the code that it runs
 * will skip delays. This allows to use [delay] in without causing the tests to take more time than necessary.
 * On JS, this function creates a `Promise` that executes the test body with the delay-skipping behavior.
 *
 * ```
 * @Test
 * fun exampleTest() = runTest {
 *     val deferred = async {
 *         delay(1_000)
 *         async {
 *             delay(1_000)
 *         }.await()
 *     }
 *
 *     deferred.await() // result available immediately
 * }
 * ```
 *
 * The platform difference entails that, in order to use this function correctly in common code, one must always
 * immediately return the produced [TestResult] from the test method, without doing anything else afterwards. See
 * [TestResult] for details on this.
 *
 * The test is run in a single thread, unless other [CoroutineDispatcher] are used for child coroutines.
 * Because of this, child coroutines are not executed in parallel to the test body.
 * In order to for the spawned-off asynchronous code to actually be executed, one must either [yield] or suspend the
 * test body some other way, or use commands that control scheduling (see [TestCoroutineScheduler]).
 *
 * ```
 * @Test
 * fun exampleWaitingForAsyncTasks1() = runTest {
 *     // 1
 *     val job = launch {
 *         // 3
 *     }
 *     // 2
 *     job.join() // the main test coroutine suspends here, so the child is executed
 *     // 4
 * }
 *
 * @Test
 * fun exampleWaitingForAsyncTasks2() = runTest {
 *     // 1
 *     launch {
 *         // 3
 *     }
 *     // 2
 *     advanceUntilIdle() // runs the tasks until their queue is empty
 *     // 4
 * }
 * ```
 *
 * ### Task scheduling
 *
 * Delay-skipping is achieved by using virtual time.
 * If [Dispatchers.Main] is set to a [TestDispatcher] via [Dispatchers.setMain] before the test,
 * then its [TestCoroutineScheduler] is used;
 * otherwise, a new one is automatically created (or taken from [context] in some way) and can be used to control
 * the virtual time, advancing it, running the tasks scheduled at a specific time etc.
 * Some convenience methods are available on [TestScope] to control the scheduler.
 *
 * Delays in code that runs inside dispatchers that don't use a [TestCoroutineScheduler] don't get skipped:
 * ```
 * @Test
 * fun exampleTest() = runTest {
 *     val elapsed = TimeSource.Monotonic.measureTime {
 *         val deferred = async {
 *             delay(1_000) // will be skipped
 *             withContext(Dispatchers.Default) {
 *                 delay(5_000) // Dispatchers.Default doesn't know about TestCoroutineScheduler
 *             }
 *         }
 *         deferred.await()
 *     }
 *     println(elapsed) // about five seconds
 * }
 * ```
 *
 * ### Failures
 *
 * #### Test body failures
 *
 * If the created coroutine completes with an exception, then this exception will be thrown at the end of the test.
 *
 * #### Reported exceptions
 *
 * Unhandled exceptions will be thrown at the end of the test.
 * If the uncaught exceptions happen after the test finishes, the error is propagated in a platform-specific manner.
 * If the test coroutine completes with an exception, the unhandled exceptions are suppressed by it.
 *
 * #### Uncompleted coroutines
 *
 * This method requires that, after the test coroutine has completed, all the other coroutines launched inside
 * [testBody] also complete, or are cancelled.
 * Otherwise, the test will be failed (which, on JVM and Native, means that [runTest] itself will throw
 * [AssertionError], whereas on JS, the `Promise` will fail with it).
 *
 * In the general case, if there are active jobs, it's impossible to detect if they are going to complete eventually due
 * to the asynchronous nature of coroutines. In order to prevent tests hanging in this scenario, [runTest] will wait
 * for [dispatchTimeoutMs] milliseconds (by default, 60 seconds) from the moment when [TestCoroutineScheduler] becomes
 * idle before throwing [AssertionError]. If some dispatcher linked to [TestCoroutineScheduler] receives a
 * task during that time, the timer gets reset.
 *
 * ### Configuration
 *
 * [context] can be used to affect the environment of the code under test. Beside just being passed to the coroutine
 * scope created for the test, [context] also can be used to change how the test is executed.
 * See the [TestScope] constructor function documentation for details.
 *
 * @throws IllegalArgumentException if the [context] is invalid. See the [TestScope] constructor docs for details.
 */
@ExperimentalCoroutinesApi
public fun runTest(
    context: CoroutineContext = EmptyCoroutineContext,
    dispatchTimeoutMs: Long = DEFAULT_DISPATCH_TIMEOUT_MS,
    testBody: suspend TestScope.() -> Unit
): TestResult {
    if (context[RunningInRunTest] != null)
        throw IllegalStateException("Calls to `runTest` can't be nested. Please read the docs on `TestResult` for details.")
    return TestScope(context + RunningInRunTest).runTest(dispatchTimeoutMs, testBody)
}

/**
 * Performs [runTest] on an existing [TestScope].
 */
@ExperimentalCoroutinesApi
public fun TestScope.runTest(
    dispatchTimeoutMs: Long = DEFAULT_DISPATCH_TIMEOUT_MS,
    testBody: suspend TestScope.() -> Unit
): TestResult = asSpecificImplementation().let {
    it.enter()
    createTestResult {
        runTestCoroutine(it, dispatchTimeoutMs, TestScopeImpl::tryGetCompletionCause, testBody) { it.leave() }
    }
}

/**
 * Runs [testProcedure], creating a [TestResult].
 */
@Suppress("NO_ACTUAL_FOR_EXPECT") // actually suppresses `TestResult`
internal expect fun createTestResult(testProcedure: suspend () -> Unit): TestResult

/** A coroutine context element indicating that the coroutine is running inside `runTest`. */
internal object RunningInRunTest : CoroutineContext.Key<RunningInRunTest>, CoroutineContext.Element {
    override val key: CoroutineContext.Key<*>
        get() = this

    override fun toString(): String = "RunningInRunTest"
}

/** The default timeout to use when waiting for asynchronous completions of the coroutines managed by
 * a [TestCoroutineScheduler]. */
internal const val DEFAULT_DISPATCH_TIMEOUT_MS = 60_000L

/**
 * Run the [body][testBody] of the [test coroutine][coroutine], waiting for asynchronous completions for at most
 * [dispatchTimeoutMs] milliseconds, and performing the [cleanup] procedure at the end.
 *
 * [tryGetCompletionCause] is the [JobSupport.completionCause], which is passed explicitly because it is protected.
 *
 * The [cleanup] procedure may either throw [UncompletedCoroutinesError] to denote that child coroutines were leaked, or
 * return a list of uncaught exceptions that should be reported at the end of the test.
 */
internal suspend fun <T: AbstractCoroutine<Unit>> runTestCoroutine(
    coroutine: T,
    dispatchTimeoutMs: Long,
    tryGetCompletionCause: T.() -> Throwable?,
    testBody: suspend T.() -> Unit,
    cleanup: () -> List<Throwable>,
) {
    val scheduler = coroutine.coroutineContext[TestCoroutineScheduler]!!
    /** TODO: moving this [AbstractCoroutine.start] call outside [createTestResult] fails on JS. */
    coroutine.start(CoroutineStart.UNDISPATCHED, coroutine) {
        testBody()
    }
    var completed = false
    while (!completed) {
        scheduler.advanceUntilIdle()
        if (coroutine.isCompleted) {
            /* don't even enter `withTimeout`; this allows to use a timeout of zero to check that there are no
               non-trivial dispatches. */
            completed = true
            continue
        }
        select<Unit> {
            coroutine.onJoin {
                completed = true
            }
            scheduler.onDispatchEvent {
                // we received knowledge that `scheduler` observed a dispatch event, so we reset the timeout
            }
            onTimeout(dispatchTimeoutMs) {
                handleTimeout(coroutine, dispatchTimeoutMs, tryGetCompletionCause, cleanup)
            }
        }
    }
    coroutine.getCompletionExceptionOrNull()?.let { exception ->
        val exceptions = try {
            cleanup()
        } catch (e: UncompletedCoroutinesError) {
            // it's normal that some jobs are not completed if the test body has failed, won't clutter the output
            emptyList()
        }
        (listOf(exception) + exceptions).throwAll()
    }
    cleanup().throwAll()
}

/**
 * Invoked on timeout in [runTest]. Almost always just builds a nice [UncompletedCoroutinesError] and throws it.
 * However, sometimes it detects that the coroutine completed, in which case it returns normally.
 */
private inline fun<T: AbstractCoroutine<Unit>> handleTimeout(
    coroutine: T,
    dispatchTimeoutMs: Long,
    tryGetCompletionCause: T.() -> Throwable?,
    cleanup: () -> List<Throwable>,
) {
    val uncaughtExceptions = try {
        cleanup()
    } catch (e: UncompletedCoroutinesError) {
        // we expect these and will instead throw a more informative exception.
        emptyList()
    }
    val activeChildren = coroutine.children.filter { it.isActive }.toList()
    val completionCause = if (coroutine.isCancelled) coroutine.tryGetCompletionCause() else null
    var message = "After waiting for $dispatchTimeoutMs ms"
    if (completionCause == null)
        message += ", the test coroutine is not completing"
    if (activeChildren.isNotEmpty())
        message += ", there were active child jobs: $activeChildren"
    if (completionCause != null && activeChildren.isEmpty()) {
        if (coroutine.isCompleted)
            return
        // TODO: can this really ever happen?
        message += ", the test coroutine was not completed"
    }
    val error = UncompletedCoroutinesError(message)
    completionCause?.let { cause -> error.addSuppressed(cause) }
    uncaughtExceptions.forEach { error.addSuppressed(it) }
    throw error
}

internal fun List<Throwable>.throwAll() {
    firstOrNull()?.apply {
        drop(1).forEach { addSuppressed(it) }
        throw this
    }
}
