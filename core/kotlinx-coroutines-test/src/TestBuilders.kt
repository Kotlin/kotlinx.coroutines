package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext


/**
 * Executes a [testBody] inside an immediate execution dispatcher.
 *
 * This is similar to [runBlocking] but it will immediately progress past delays and into [launch] and [async] blocks.
 * You can use this to write tests that execute in the presence of calls to [delay] without causing your test to take
 * extra time.
 **
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
 * @param context An optional context that MAY contain a [DelayController] and/or [TestCoroutineExceptionHandler]
 * @param testBody The code of the unit-test.
 */
fun runBlockingTest(context: CoroutineContext? = null, testBody: suspend TestCoroutineScope.() -> Unit) {
    val (safeContext, dispatcher) = context.checkArguments()
    // smart cast dispatcher to expose interface
    dispatcher as DelayController

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

private fun CoroutineContext.activeJobs() =
        checkNotNull(this[Job]).children.filter { it.isActive }.toSet()

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