/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*

/**
 * Executes a [testBody] inside an immediate execution dispatcher.
 *
 * This is similar to [runBlocking] but it will immediately progress past delays and into [launch] and [async] blocks.
 * You can use this to write tests that execute in the presence of calls to [delay] without causing your test to take
 * extra time.
 *
 * ```
 * @Test
 * fun exampleTest() = runBlockingTest {
 *     val deferred = async {
 *         delay(1_000)
 *         async {
 *             delay(1_000)
 *         }.await()
 *     }
 *
 *     deferred.await() // result available immediately
 * }
 *
 * ```
 *
 * This method requires that all coroutines launched inside [testBody] complete, or are cancelled, as part of the test
 * conditions.
 *
 * Unhandled exceptions thrown by coroutines in the test will be re-thrown at the end of the test.
 *
 * @throws AssertionError If the [testBody] does not complete (or cancel) all coroutines that it launches
 * (including coroutines suspended on join/await).
 *
 * @param context additional context elements. If [context] contains [CoroutineDispatcher] or [CoroutineExceptionHandler],
 *        then they must implement [DelayController] and [TestCoroutineExceptionHandler] respectively.
 * @param testBody The code of the unit-test.
 */
@Deprecated("Use `runTest` instead to support completing from other dispatchers.", level = DeprecationLevel.WARNING)
public fun runBlockingTest(context: CoroutineContext = EmptyCoroutineContext, testBody: suspend TestCoroutineScope.() -> Unit) {
    val scope = TestCoroutineScope(TestCoroutineDispatcher() + SupervisorJob() + context)
    val scheduler = scope.testScheduler
    val deferred = scope.async {
        scope.testBody()
    }
    scheduler.advanceUntilIdle()
    deferred.getCompletionExceptionOrNull()?.let {
        throw it
    }
    scope.cleanupTestCoroutines()
}

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineScope].
 */
// todo: need documentation on how this extension is supposed to be used
@Deprecated("Use `runTest` instead to support completing from other dispatchers.", level = DeprecationLevel.WARNING)
public fun TestCoroutineScope.runBlockingTest(block: suspend TestCoroutineScope.() -> Unit): Unit =
    runBlockingTest(coroutineContext, block)

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineDispatcher].
 */
@Deprecated("Use `runTest` instead to support completing from other dispatchers.", level = DeprecationLevel.WARNING)
public fun TestCoroutineDispatcher.runBlockingTest(block: suspend TestCoroutineScope.() -> Unit): Unit =
    runBlockingTest(this, block)

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
@DelicateCoroutinesApi
public expect class TestResult

/**
 * Executes [testBody] as a test, returning [TestResult].
 *
 * On JVM and Native, this function behaves similarly to [runBlocking], with the difference that the code that it runs
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
 * ### Delay-skipping
 *
 * Delay-skipping is achieved by using virtual time. [TestCoroutineScheduler] is automatically created (if it wasn't
 * passed in some way in [context]) and can be used to control the virtual time, advancing it, running the tasks
 * scheduled at a specific time etc. Some convenience methods are available on [TestCoroutineScope] to control the
 * scheduler.
 *
 * Delays in code that runs inside dispatchers that don't use a [TestCoroutineScheduler] don't get skipped:
 * ```
 * @Test
 * fun exampleTest() = runTest {
 *     val elapsed = TimeSource.Monotonic.measureTime {
 *         val deferred = async {
 *             delay(1_000) // will be skipped
 *             withContext(Dispatchers.Default) {
 *                 delay(5_000) // Dispatchers.Default don't know about TestCoroutineScheduler
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
 * If the test body finishes with an exception, then this exception will be thrown at the end of the test. Additionally,
 * to prevent child coroutines getting stuck, the whole scope will be cancelled in this case.
 *
 * #### Reported exceptions
 *
 * Exceptions reported to the test coroutine scope via [TestCoroutineScope.reportException] will be thrown at the end.
 * By default (without passing an explicit [TestExceptionHandler]), this includes all unhandled exceptions.
 *
 * #### Uncompleted coroutines
 *
 * This method requires that all coroutines launched inside [testBody] complete, or are cancelled. Otherwise, the test
 * will be failed (which, on JVM and Native, means that [runTest] itself will throw [AssertionError],
 * whereas on JS, the `Promise` will fail with it).
 *
 * In the general case, if there are active jobs, it's impossible to detect if they are going to complete eventually due
 * to the asynchronous nature of coroutines. In order to prevent tests hanging in this scenario, [runTest] will wait
 * for [dispatchTimeoutMs] milliseconds (by default, 10 seconds) from the moment when [TestCoroutineScheduler] becomes
 * idle before throwing [AssertionError]. If some dispatcher linked to [TestCoroutineScheduler] receives a
 * task during that time, the timer gets reset.
 *
 * ### Configuration
 *
 * [context] can be used to affect the environment of the code under test. Beside just being passed to the coroutine
 * scope created for the test, [context] also can be used to change how the test is executed.
 * See the [TestCoroutineScope] constructor documentation for details.
 *
 * @throws IllegalArgumentException if the [context] is invalid. See the [TestCoroutineScope] constructor docs for
 * details.
 */
@DelicateCoroutinesApi
public fun runTest(
    context: CoroutineContext = EmptyCoroutineContext,
    dispatchTimeoutMs: Long = DEFAULT_DISPATCH_TIMEOUT_MS,
    testBody: suspend TestCoroutineScope.() -> Unit
): TestResult {
    if (context[RunningInRunTest] != null)
        throw IllegalStateException("Calls to `runTest` can't be nested. Please read the docs on `TestResult` for details.")
    val testScope = TestBodyCoroutine<Unit>(TestCoroutineScope(context + RunningInRunTest()))
    val scheduler = testScope.testScheduler
    testScope.start(CoroutineStart.DEFAULT, testScope) {
        testBody()
    }
    return createTestResult {
        var completed = false
        while (!completed) {
            scheduler.advanceUntilIdle()
            if (testScope.isCompleted) {
                /* don't even enter `withTimeout`; this allows to use a timeout of zero to check that there are no
                   non-trivial dispatches. */
                completed = true
                continue
            }
            try {
                withTimeout(dispatchTimeoutMs) {
                    select<Unit> {
                        testScope.onJoin {
                            completed = true
                        }
                        scheduler.onDispatchEvent {
                            // we received knowledge that `scheduler` observed a dispatch event, so we reset the timeout
                        }
                    }
                }
            } catch (e: TimeoutCancellationException) {
                try {
                    testScope.cleanupTestCoroutines()
                } catch (e: UncompletedCoroutinesError) {
                    // we expect these and will instead throw a more informative exception just below.
                }
                throw UncompletedCoroutinesError("The test coroutine was not completed after waiting for $dispatchTimeoutMs ms")
            }
        }
        testScope.getCompletionExceptionOrNull()?.let {
            try {
                testScope.cleanupTestCoroutines()
            } catch (e: UncompletedCoroutinesError) {
                // it's normal that some jobs are not completed if the test body has failed, won't clutter the output
            } catch (e: Throwable) {
                e.printStackTrace()
            }
            throw it
        }
        testScope.cleanupTestCoroutines()
    }
}

/**
 * Runs [testProcedure], creating a [TestResult].
 */
@Suppress("NO_ACTUAL_FOR_EXPECT") // actually suppresses `TestResult`
internal expect fun createTestResult(testProcedure: suspend () -> Unit): TestResult

/**
 * Runs a test in a [TestCoroutineScope] based on this one.
 *
 * Calls [runTest] using a coroutine context from this [TestCoroutineScope]. The [TestCoroutineScope] used to run
 * [block] will be different from this one, but will use its [Job] as a parent; therefore, even if calling
 * [TestCoroutineScope.cleanupTestCoroutines] on this scope were to complete its job, [runTest] won't complete it at the
 * end of the test.
 *
 * Since this function returns [TestResult], in order to work correctly on the JS, its result must be returned
 * immediately from the test body. See the docs for [TestResult] for details.
 */
@DelicateCoroutinesApi
public fun TestCoroutineScope.runTest(
    dispatchTimeoutMs: Long = DEFAULT_DISPATCH_TIMEOUT_MS,
    block: suspend TestCoroutineScope.() -> Unit
): TestResult =
    runTest(coroutineContext, dispatchTimeoutMs, block)

/**
 * Run a test using this [TestDispatcher].
 *
 * A convenience function that calls [runTest] with the given arguments.
 *
 * Since this function returns [TestResult], in order to work correctly on the JS, its result must be returned
 * immediately from the test body. See the docs for [TestResult] for details.
 */
@DelicateCoroutinesApi
public fun TestDispatcher.runTest(
    dispatchTimeoutMs: Long = DEFAULT_DISPATCH_TIMEOUT_MS,
    block: suspend TestCoroutineScope.() -> Unit
): TestResult =
    runTest(this, dispatchTimeoutMs, block)

/** A coroutine context element indicating that the coroutine is running inside `runTest`. */
private class RunningInRunTest: AbstractCoroutineContextElement(RunningInRunTest), CoroutineContext.Element {
    companion object Key : CoroutineContext.Key<RunningInRunTest>
}

/** The default timeout to use when waiting for asynchronous completions of the coroutines managed by
 * a [TestCoroutineScheduler]. */
private const val DEFAULT_DISPATCH_TIMEOUT_MS = 10_000L

private class TestBodyCoroutine<T>(
    private val testScope: TestCoroutineScope,
) : AbstractCoroutine<T>(testScope.coroutineContext, initParentJob = true, active = true), TestCoroutineScope
{
    override val testScheduler get() = testScope.testScheduler

    override fun cleanupTestCoroutines() = testScope.cleanupTestCoroutines()

    override fun reportException(throwable: Throwable) = testScope.reportException(throwable)
}
