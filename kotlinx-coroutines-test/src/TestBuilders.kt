/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.selects.select
import kotlin.coroutines.*

private const val DEFAULT_WAIT_FOR_OTHER_DISPATCHERS = 30_000L

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
 * then they must implement [DelayController] and [TestCoroutineExceptionHandler] respectively.
 * @param waitForOtherDispatchers how long to wait for other dispatchers to execute tasks asynchronously, default 30
 * seconds
 * @param testBody The code of the unit-test.
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun runBlockingTest(
        context: CoroutineContext = EmptyCoroutineContext,
        waitForOtherDispatchers: Long = DEFAULT_WAIT_FOR_OTHER_DISPATCHERS,
        testBody: suspend TestCoroutineScope.() -> Unit
) {
    val (safeContext, dispatcher) = context.checkArguments()
    val startingJobs = safeContext.activeJobs()

    var testScope: TestCoroutineScope? = null

    val deferred = CoroutineScope(safeContext).async {
        val localTestScope = TestCoroutineScope(coroutineContext)
        testScope = localTestScope
        localTestScope.testBody()
    }

    val didTimeout = deferred.waitForCompletion(waitForOtherDispatchers, dispatcher, dispatcher as IdleWaiter)

    if (deferred.isCompleted) {
        deferred.getCompletionExceptionOrNull()?.let {
            throw it
        }
    }

    testScope!!.cleanupTestCoroutines()
    val endingJobs = safeContext.activeJobs()

    // TODO: should these be separate exceptions to allow for tests to detect difference?
    if (didTimeout) {
        val message = """
            runBlockingTest timed out after waiting ${waitForOtherDispatchers}ms for coroutines to complete.
            Active jobs after test (may be empty): $endingJobs
            """.trimIndent()
        throw UncompletedCoroutinesError(message)
    } else if ((endingJobs - startingJobs).isNotEmpty()) {
        throw UncompletedCoroutinesError("Test finished with active jobs: $endingJobs ")
    }
}

private fun Deferred<Unit>.waitForCompletion(wait: Long, delayController: DelayController, park: IdleWaiter): Boolean {
    var didTimeout = false

    runBlocking {
        val unparkChannel = Channel<Unit>(1)
        val job = launch {
            while(true) {
                park.suspendUntilNextDispatch()
                unparkChannel.send(Unit)
            }
        }

        try {
            withTimeout(wait) {
                while(!isCompleted) {
                    delayController.advanceUntilIdle()
                    select<Unit> {
                        onAwait { Unit }
                        unparkChannel.onReceive { Unit }
                    }
                }
            }
        } catch (exception: TimeoutCancellationException) {
            didTimeout = true
        }
        job.cancel()
    }
    return didTimeout
}

private fun CoroutineContext.activeJobs(): Set<Job> {
    return checkNotNull(this[Job]).children.filter { it.isActive }.toSet()
}

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineScope].
 */
// todo: need documentation on how this extension is supposed to be used
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun TestCoroutineScope.runBlockingTest(waitForOtherDispatchers: Long = DEFAULT_WAIT_FOR_OTHER_DISPATCHERS, block: suspend TestCoroutineScope.() -> Unit) = runBlockingTest(coroutineContext, waitForOtherDispatchers, block)

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineDispatcher].
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun TestCoroutineDispatcher.runBlockingTest(waitForOtherDispatchers: Long = DEFAULT_WAIT_FOR_OTHER_DISPATCHERS, block: suspend TestCoroutineScope.() -> Unit) = runBlockingTest(this, waitForOtherDispatchers, block)

private fun CoroutineContext.checkArguments(): Pair<CoroutineContext, DelayController> {
    // TODO optimize it
    val dispatcher = get(ContinuationInterceptor).run {
        this?.let { require(this is DelayController) { "Dispatcher must implement DelayController: $this" } }
        this?.let { require(this is IdleWaiter) { "Dispatcher must implement IdleWaiter" } }
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
