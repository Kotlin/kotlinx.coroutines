package kotlinx.coroutines.test

import kotlinx.coroutines.*
import java.util.concurrent.TimeoutException
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.coroutineContext

/**
 * Executes a [testBody] in a [TestCoroutineScope] which provides detailed control over the execution of coroutines.
 *
 * This function should be used when you need detailed control over the execution of your test. For most tests consider
 * using [runBlockingTest].
 *
 * Code executed in a `asyncTest` will dispatch lazily. That means calling builders such as [launch] or [async] will
 * not execute the block immediately. You can use methods like [TestCoroutineScope.runCurrent] and
 * [TestCoroutineScope.advanceTimeTo] on the [TestCoroutineScope]. For a full list of execution methods see
 * [DelayController].
 *
 * ```
 * @Test
 * fun exampleTest() = asyncTest {
 *     // 1: launch will execute but not run the body
 *     launch  {
 *         // 3: the body of launch will execute in response to runCurrent [currentTime = 0ms]
 *         delay(1_000)
 *         // 5: After the time is advanced, delay(1_000) will return [currentTime = 1000ms]
 *         println("Faster delays!")
 *     }
 *
 *     // 2: use runCurrent() to execute the body of launch [currentTime = 0ms]
 *     runCurrent()
 *
 *     // 4: advance the dispatcher "time" by 1_000, which will resume after the delay
 *     advanceTimeTo(1_000)
 *
 * ```
 *
 * This method requires that all coroutines launched inside [testBody] complete, or are cancelled, as part of the test
 * conditions.
 *
 * In addition any unhandled exceptions thrown in coroutines must be rethrown by
 * [TestCoroutineScope.rethrowUncaughtCoroutineException] or cleared via [TestCoroutineScope.exceptions] inside of
 * [testBody].
 *
 * @throws UncompletedCoroutinesError If the [testBody] does not complete (or cancel) all coroutines that it launches
 * (including coroutines suspended on await).
 * @throws Throwable If an uncaught exception was captured by this test it will be rethrown.
 *
 * @param context An optional dispatcher, during [testBody] execution [DelayController.dispatchImmediately] will be set to false
 * @param testBody The code of the unit-test.
 *
 * @see [runBlockingTest]
 */
fun asyncTest(context: CoroutineContext? = null, testBody: TestCoroutineScope.() -> Unit) {
    val (safeContext, dispatcher) = context.checkArguments()
    // smart cast dispatcher to expose interface
    dispatcher as DelayController
    val scope = TestCoroutineScope(safeContext)

    val oldDispatch = dispatcher.dispatchImmediately
    dispatcher.dispatchImmediately = false

    try {
        scope.testBody()
        scope.cleanupTestCoroutines()

        // check for any active child jobs after cleanup (e.g. coroutines suspended on calls to await)
        val job = checkNotNull(safeContext[Job]) { "Job required for asyncTest" }
        val activeChildren = job.children.filter { it.isActive }.toList()
        if (activeChildren.isNotEmpty()) {
            throw UncompletedCoroutinesError("Test finished with active jobs: ${activeChildren}")
        }
    } finally {
        dispatcher.dispatchImmediately = oldDispatch
    }
}

/**
 * @see [asyncTest]
 */
fun TestCoroutineScope.asyncTest(testBody: TestCoroutineScope.() -> Unit) =
        asyncTest(coroutineContext, testBody)

/**
 * This method is deprecated.
 *
 * @see [cleanupTestCoroutines]
 */
@Deprecated("This API has been deprecated to integrate with Structured Concurrency.",
        ReplaceWith("scope.runBlockingTest(testBody)", "kotlinx.coroutines.test"),
        level = DeprecationLevel.ERROR)
fun withTestContext(scope: TestCoroutineScope, testBody: suspend TestCoroutineScope.() -> Unit) {
    scope.runBlockingTest(testBody)
}

/**
 * Executes a [testBody] inside an immediate execution dispatcher.
 *
 * This is similar to [runBlocking] but it will immediately progress past delays and into [launch] and [async] blocks.
 * You can use this to write tests that execute in the presence of calls to [delay] without causing your test to take
 * extra time.
 *
 * Compared to [asyncTest], it provides a smaller API for tests that don't need detailed control over execution.
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
 * In unhandled exceptions inside coroutines will not fail the test.
 *
 * @throws UncompletedCoroutinesError If the [testBody] does not complete (or cancel) all coroutines that it launches
 * (including coroutines suspended on await).
 *
 * @param context An optional context, during [testBody] execution [DelayController.dispatchImmediately] will be set to true
 * @param testBody The code of the unit-test.
 *
 * @see [asyncTest]
 */
fun runBlockingTest(context: CoroutineContext? = null, testBody: suspend TestCoroutineScope.() -> Unit) {
    val (safeContext, dispatcher) = context.checkArguments()
    // smart cast dispatcher to expose interface
    dispatcher as DelayController

    val oldDispatch = dispatcher.dispatchImmediately
    dispatcher.dispatchImmediately = true
    val scope = TestCoroutineScope(safeContext)
    try {

        val deferred = scope.async {
            scope.testBody()
        }
        dispatcher.advanceUntilIdle()
        deferred.getCompletionExceptionOrNull()?.let {
            throw it
        }
        scope.cleanupTestCoroutines()
        val activeChildren = checkNotNull(safeContext[Job]).children.filter { it.isActive }.toList()
        if (activeChildren.isNotEmpty()) {
            throw UncompletedCoroutinesError("Test finished with active jobs: ${activeChildren}")
        }
    } finally {
        dispatcher.dispatchImmediately = oldDispatch
    }
}

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineScope].
 */
fun TestCoroutineScope.runBlockingTest(block: suspend TestCoroutineScope.() -> Unit) {
    runBlockingTest(coroutineContext, block)
}

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineDispatcher].
 *
 */
fun TestCoroutineDispatcher.runBlockingTest(block: suspend TestCoroutineScope.() -> Unit) {
    runBlockingTest(this, block)
}

private fun CoroutineContext?.checkArguments(): Pair<CoroutineContext, ContinuationInterceptor> {
    var safeContext= this ?: TestCoroutineExceptionHandler() + TestCoroutineDispatcher()

    val dispatcher = safeContext[ContinuationInterceptor].run {
        this?.let {
            require(this is DelayController) { "Dispatcher must implement DelayController" }
        }
        this ?: TestCoroutineDispatcher()
    }

    val exceptionHandler = safeContext[CoroutineExceptionHandler].run {
        this?.let {
            require(this is ExceptionCaptor) { "coroutineExceptionHandler must implement ExceptionCaptor" }
        }
        this ?: TestCoroutineExceptionHandler()
    }

    val job = safeContext[Job] ?: SupervisorJob()

    safeContext = safeContext + dispatcher + exceptionHandler + job
    return Pair(safeContext, dispatcher)
}