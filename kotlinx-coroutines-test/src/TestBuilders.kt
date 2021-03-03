/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
    dispatcher.advanceUntilIdle()
    deferred.getCompletionExceptionOrNull()?.let {
        throw it
    }
    scope.cleanupTestCoroutines()
    val endingJobs = safeContext.activeJobs()
    if ((endingJobs - startingJobs).isNotEmpty()) {
        throw UncompletedCoroutinesError("Test finished with active jobs: $endingJobs")
    }
}

private fun CoroutineContext.activeJobs(): Set<Job> {
    return checkNotNull(this[Job]).children.filter { it.isActive }.toSet()
}

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineScope].
 */
// todo: need documentation on how this extension is supposed to be used
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun TestCoroutineScope.runBlockingTest(block: suspend TestCoroutineScope.() -> Unit): Unit =
    runBlockingTest(coroutineContext, block)

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineDispatcher].
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun TestCoroutineDispatcher.runBlockingTest(block: suspend TestCoroutineScope.() -> Unit): Unit =
    runBlockingTest(this, block)

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
