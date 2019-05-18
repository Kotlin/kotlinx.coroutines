/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
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
 * @throws UncompletedCoroutinesError If the [testBody] does not complete (or cancel) all coroutines that it launches
 * (including coroutines suspended on join/await).
 *
 * @param context additional context elements. If [context] contains [CoroutineDispatcher] or [CoroutineExceptionHandler],
 *        then they must implement [DelayController] and [TestCoroutineExceptionHandler] respectively.
 * @param testBody The code of the unit-test.
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun runBlockingTest(context: CoroutineContext = EmptyCoroutineContext, testBody: suspend TestCoroutineScope.() -> Unit) {
    val (safeContext, dispatcher) = context.checkArguments()
    val startingJobs = safeContext.activeJobs()
    val scope = TestCoroutineScope(safeContext)

    val deferred = scope.async {
        scope.testBody()
    }

    // run any outstanding coroutines that can be completed by advancing virtual-time
    dispatcher.advanceUntilIdle()

    // fetch results from the coroutine - this may require a thread hop if some child coroutine was *completed* on
    // another thread during this test so we must use an invokeOnCompletion handler to retrieve the result.

    // There are two code paths for fetching the error:
    //
    // 1. The job was already completed (happy path, normal test)
    //    - invokeOnCompletion was executed immediately and errorThrownByTestOrNull is already at it's final value so
    //      we can throw it
    // 2. The job has not already completed (always fail the test due to error or time-based non-determinism)
    //    - invokeOnCompletion will not be triggered right away. To avoid introducing wall non-deterministic  behavior
    //      (the deferred may complete between here and the call to activeJobs below) this will always be considered a
    //      test failure.
    //    - this will not happen if all coroutines are only waiting to complete due to thread hops, but may happen
    //      if another thread triggers completion concurrently with this cleanup code.
    //
    // give test code errors a priority in the happy path, throw here if the error is already known.
    val (wasCompletedAfterTest, errorThrownByTestOrNull) = deferred.getResultIfKnown()
    errorThrownByTestOrNull?.let { throw it }

    scope.cleanupTestCoroutines()
    val endingJobs = safeContext.activeJobs()
    if ((endingJobs - startingJobs).isNotEmpty()) {
        throw UncompletedCoroutinesError("Test finished with active jobs: $endingJobs")
    }

    if (!wasCompletedAfterTest) {
        // Handle path #2, we are going to fail the test in an opinionated way at this point so let the developer know
        // how to fix it.
        throw UncompletedCoroutinesError("Test completed all jobs after cleanup code started. This is " +
                "thrown to avoid non-deterministic behavior in tests (the next execution may fail randomly). Ensure " +
                "all threads started by the test are completed before returning from runBlockingTest.")
    }
}

private fun Deferred<Unit>.getResultIfKnown(): Pair<Boolean, Throwable?> {
    var testError: Throwable? = null
    var wasExecuted = false
    invokeOnCompletion { errorFromTestOrNull ->
        testError = errorFromTestOrNull
        wasExecuted = true
    }.dispose()
    return Pair(wasExecuted, testError)
}

private fun CoroutineContext.activeJobs(): Set<Job> {
    return checkNotNull(this[Job]).children.filter { it.isActive }.toSet()
}

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineScope].
 */
// todo: need documentation on how this extension is supposed to be used
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun TestCoroutineScope.runBlockingTest(block: suspend TestCoroutineScope.() -> Unit) = runBlockingTest(coroutineContext, block)

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineDispatcher].
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun TestCoroutineDispatcher.runBlockingTest(block: suspend TestCoroutineScope.() -> Unit) = runBlockingTest(this, block)

private fun CoroutineContext.checkArguments(): Pair<CoroutineContext, DelayController> {
    // TODO optimize it
    val dispatcher = get(ContinuationInterceptor).run {
        this?.let { require(this is DelayController) { "Dispatcher must implement DelayController: $this" } }
        this ?: TestCoroutineDispatcher()
    }

    val exceptionHandler =  get(CoroutineExceptionHandler).run {
        this?.let {
            require(this is UncaughtExceptionCaptor) { "coroutineExceptionHandler must implement UncaughtExceptionCaptor: $this" }
        }
        this ?: TestCoroutineExceptionHandler()
    }

    val job = get(Job) ?: SupervisorJob()
    return Pair(this + dispatcher + exceptionHandler + job, dispatcher as DelayController)
}
