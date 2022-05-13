/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("DEPRECATION")
@file:JvmName("TestBuildersKt")
@file:JvmMultifileClass

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * Executes a [testBody] inside an immediate execution dispatcher.
 *
 * This method is deprecated in favor of [runTest]. Please see the
 * [migration guide](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-test/MIGRATION.md)
 * for an instruction on how to update the code for the new API.
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
@Deprecated("Use `runTest` instead to support completing from other dispatchers. " +
    "Please see the migration guide for details: " +
    "https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-test/MIGRATION.md",
    level = DeprecationLevel.WARNING)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public fun runBlockingTest(
    context: CoroutineContext = EmptyCoroutineContext,
    testBody: suspend TestCoroutineScope.() -> Unit
) {
    val scope = createTestCoroutineScope(TestCoroutineDispatcher() + SupervisorJob() + context)
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
 * A version of [runBlockingTest] that works with [TestScope].
 */
@Deprecated("Use `runTest` instead to support completing from other dispatchers.", level = DeprecationLevel.WARNING)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public fun runBlockingTestOnTestScope(
    context: CoroutineContext = EmptyCoroutineContext,
    testBody: suspend TestScope.() -> Unit
) {
    val completeContext = TestCoroutineDispatcher() + SupervisorJob() + context
    val startJobs = completeContext.activeJobs()
    val scope = TestScope(completeContext).asSpecificImplementation()
    scope.enter()
    scope.start(CoroutineStart.UNDISPATCHED, scope) {
        scope.testBody()
    }
    scope.testScheduler.advanceUntilIdle()
    try {
        scope.getCompletionExceptionOrNull()
    } catch (e: IllegalStateException) {
        null // the deferred was not completed yet; `scope.leave()` should complain then about unfinished jobs
    }?.let {
        val exceptions = try {
            scope.leave()
        } catch (e: UncompletedCoroutinesError) {
            listOf()
        }
        (listOf(it) + exceptions).throwAll()
        return
    }
    scope.leave().throwAll()
    val jobs = completeContext.activeJobs() - startJobs
    if (jobs.isNotEmpty())
        throw UncompletedCoroutinesError("Some jobs were not completed at the end of the test: $jobs")
}

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineScope].
 *
 * This method is deprecated in favor of [runTest], whereas [TestCoroutineScope] is deprecated in favor of [TestScope].
 * Please see the
 * [migration guide](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-test/MIGRATION.md)
 * for an instruction on how to update the code for the new API.
 */
@Deprecated("Use `runTest` instead to support completing from other dispatchers. " +
    "Please see the migration guide for details: " +
    "https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-test/MIGRATION.md",
    level = DeprecationLevel.WARNING)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public fun TestCoroutineScope.runBlockingTest(block: suspend TestCoroutineScope.() -> Unit): Unit =
    runBlockingTest(coroutineContext, block)

/**
 * Convenience method for calling [runBlockingTestOnTestScope] on an existing [TestScope].
 */
@Deprecated("Use `runTest` instead to support completing from other dispatchers.", level = DeprecationLevel.WARNING)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public fun TestScope.runBlockingTest(block: suspend TestScope.() -> Unit): Unit =
    runBlockingTestOnTestScope(coroutineContext, block)

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineDispatcher].
 *
 * This method is deprecated in favor of [runTest], whereas [TestCoroutineScope] is deprecated in favor of [TestScope].
 * Please see the
 * [migration guide](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-test/MIGRATION.md)
 * for an instruction on how to update the code for the new API.
 */
@Deprecated("Use `runTest` instead to support completing from other dispatchers. " +
    "Please see the migration guide for details: " +
    "https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-test/MIGRATION.md",
    level = DeprecationLevel.WARNING)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public fun TestCoroutineDispatcher.runBlockingTest(block: suspend TestCoroutineScope.() -> Unit): Unit =
    runBlockingTest(this, block)

/**
 * This is an overload of [runTest] that works with [TestCoroutineScope].
 */
@ExperimentalCoroutinesApi
@Deprecated("Use `runTest` instead.", level = DeprecationLevel.WARNING)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public fun runTestWithLegacyScope(
    context: CoroutineContext = EmptyCoroutineContext,
    dispatchTimeoutMs: Long = DEFAULT_DISPATCH_TIMEOUT_MS,
    testBody: suspend TestCoroutineScope.() -> Unit
): TestResult {
    if (context[RunningInRunTest] != null)
        throw IllegalStateException("Calls to `runTest` can't be nested. Please read the docs on `TestResult` for details.")
    val testScope = TestBodyCoroutine(createTestCoroutineScope(context + RunningInRunTest))
    return createTestResult {
        runTestCoroutine(testScope, dispatchTimeoutMs, TestBodyCoroutine::tryGetCompletionCause, testBody) {
            try {
                testScope.cleanup()
                emptyList()
            } catch (e: UncompletedCoroutinesError) {
                throw e
            } catch (e: Throwable) {
                listOf(e)
            }
        }
    }
}

/**
 * Runs a test in a [TestCoroutineScope] based on this one.
 *
 * Calls [runTest] using a coroutine context from this [TestCoroutineScope]. The [TestCoroutineScope] used to run the
 * [block] will be different from this one, but will use its [Job] as a parent.
 *
 * Since this function returns [TestResult], in order to work correctly on the JS, its result must be returned
 * immediately from the test body. See the docs for [TestResult] for details.
 */
@ExperimentalCoroutinesApi
@Deprecated("Use `TestScope.runTest` instead.", level = DeprecationLevel.WARNING)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public fun TestCoroutineScope.runTest(
    dispatchTimeoutMs: Long = DEFAULT_DISPATCH_TIMEOUT_MS,
    block: suspend TestCoroutineScope.() -> Unit
): TestResult = runTestWithLegacyScope(coroutineContext, dispatchTimeoutMs, block)

private class TestBodyCoroutine(
    private val testScope: TestCoroutineScope,
) : AbstractCoroutine<Unit>(testScope.coroutineContext, initParentJob = true, active = true), TestCoroutineScope {

    override val testScheduler get() = testScope.testScheduler

    @Deprecated(
        "This deprecation is to prevent accidentally calling `cleanupTestCoroutines` in our own code.",
        ReplaceWith("this.cleanup()"),
        DeprecationLevel.ERROR
    )
    override fun cleanupTestCoroutines() =
        throw UnsupportedOperationException(
            "Calling `cleanupTestCoroutines` inside `runTest` is prohibited: " +
                "it will be called at the end of the test in any case."
        )

    fun cleanup() = testScope.cleanupTestCoroutines()

    /** Throws an exception if the coroutine is not completing. */
    fun tryGetCompletionCause(): Throwable? = completionCause
}
