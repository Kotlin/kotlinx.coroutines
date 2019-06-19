/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.select
import java.lang.StringBuilder
import kotlin.coroutines.*

private const val DEFAULT_TEST_TIMEOUT = 30_000L

/**
 * A strategy for waiting on coroutines executed on other dispatchers inside a [runBlockingTest].
 *
 * Most tests should use [MultiDispatcherWaitConfig]. As an optimization, a test that executes coroutines only on a
 * [TestCoroutineDispatcher] and never interacts with other dispatchers may use [SingleDispatcherWaitConfig].
 *
 * A test may subclass this to customize the wait in advanced cases.
 */
interface WaitConfig {
    /**
     * How long (in wall-clock time) to wait for other Dispatchers to complete coroutines during a [runBlockingTest].
     *
     * This delay is not related to the virtual time of a [TestCoroutineDispatcher], but is how long a test should allow
     * another dispatcher, like Dispatchers.IO, to perform a time consuming activity such as reading from a database.
     */
    val wait: Long
}

/**
 * Do not wait for coroutines executing on another [Dispatcher] in [runBlockingTest].

 * Always fails with an uncompleted coroutine when any coroutine in the test executes on any other dispatcher (including
 * calls to [withContext]). It should not be used for most tests, instead use the default value of
 * [MultiDispatcherWaitConfig].
 *
 * This configuration should only be used as an optimization for tests that intentionally create an uncompleted
 * coroutine and execute all coroutines on the [TestCoroutineDispatcher] used by [runBlockingTest].
 *
 * If in doubt, prefer [MultiDispatcherWaitConfig].
 */
object SingleDispatcherWaitConfig : WaitConfig {
    /**
     * This value is ignored by [runBlockingTest] on [SingleDispatcherWaitConfig]
     */
    override val wait = 0L

    override fun toString() = "SingleDispatcherWaitConfig"
}

/**
 * Wait up to 30 seconds for any coroutines running on another [Dispatcher] to complete in [runBlockingTest].
 *
 * This is the default value for [runBlockingTest] and the recommendation for most tests. This configuration will allow
 * for coroutines to be launched on another dispatcher inside the test (e.g. calls to `withContext(Dispatchers.IO)`).
 *
 * This allows for code like the following to be tested correctly using [runBlockingTest]:
 *
 * ```
 * suspend fun delayOnDefault() = withContext(Dispatchers.Default) {
 *      // this delay does not use the virtual-time of runBlockingTest since it's executing on Dispatchers.Default
 *     delay(50)
 * }
 *
 * runBlockingTest {
 *     // Note: This test takes at least 50ms (real time) to run
 *
 *     // delayOnDefault will suspend the runBlockingTest coroutine for 50ms      [real-time: 0; virtual-time: 0]
 *     delayOnDefault()
 *     // runBlockingTest resumes 50ms later (real time)                          [real-time: 50; virtual-time: 0]
 *
 *     delay(10)
 *     //this delay will auto-progress since it's in runBlockingTest              [real-time: 50; virtual-time: 10]
 * }
 * ```
 */
object MultiDispatcherWaitConfig: WaitConfig {
    /**
     * Default wait is 30 seconds.
     *
     * {@inheritDoc}
     */
    override val wait = DEFAULT_TEST_TIMEOUT

    override fun toString() = "MultiDispatcherWaitConfig[wait = 30s]"
}

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
 * @param waitConfig strategy for waiting on other dispatchers to complete during the test. [SingleDispatcherWaitConfig]
 * will never wait, other values will wait for [WaitConfig.wait]ms.
 * @param testBody The code of the unit-test.
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun runBlockingTest(
        context: CoroutineContext = EmptyCoroutineContext,
        waitConfig: WaitConfig = MultiDispatcherWaitConfig,
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

    val didTimeout = deferred.waitForCompletion(waitConfig, dispatcher)

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
            runBlockingTest timed out after waiting ${waitConfig.wait}ms for coroutines to complete due waitConfig = $waitConfig. 
            Active jobs after test (may be empty): $endingJobs
            """.trimIndent()
        throw UncompletedCoroutinesError(message)
    } else if ((endingJobs - startingJobs).isNotEmpty()) {
        val message = StringBuilder("Test finished with active jobs: ")
        message.append(endingJobs)
        if (waitConfig == SingleDispatcherWaitConfig) {
            message.append("""

            Note: runBlockingTest did not wait for other dispatchers due to argument waitConfig = $waitConfig
            
            Tip: If this runBlockingTest starts any code on another dispatcher (such as Dispatchers.Default, 
            Dispatchers.IO, etc) in any of the functions it calls it will never pass when configured with 
            SingleDispatcherWaitConfig. Please update your test to use the default value of MultiDispatcherWaitConfig
            like:
            
                runBlockingTest { }
            
            """.trimIndent())
        }
        throw UncompletedCoroutinesError(message.toString())
    }
}

private fun Deferred<Unit>.waitForCompletion(waitConfig: WaitConfig, dispatcher: DelayController): Boolean {
    var didTimeout = false
    when (waitConfig) {
        SingleDispatcherWaitConfig -> dispatcher.advanceUntilIdle()
        else -> {
            runBlocking {
                val subscription = dispatcher.queueState.openSubscription()
                dispatcher.advanceUntilIdle()

                var finished = false
                try {
                    while (!finished) {
                        finished = select {
                            this@waitForCompletion.onAwait {
                                true
                            }
                            onTimeout(waitConfig.wait) {
                                didTimeout = true
                                true
                            }
                            subscription.onReceive { queueState ->
                                when (queueState) {
                                    DelayController.QueueState.Idle -> Unit
                                    else -> dispatcher.advanceUntilIdle()
                                }
                                false
                            }
                        }
                    }
                } finally {
                    subscription.cancel()
                }
            }

        }
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
public fun TestCoroutineScope.runBlockingTest(configuration: WaitConfig = MultiDispatcherWaitConfig, block: suspend TestCoroutineScope.() -> Unit) = runBlockingTest(coroutineContext, configuration, block)

/**
 * Convenience method for calling [runBlockingTest] on an existing [TestCoroutineDispatcher].
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun TestCoroutineDispatcher.runBlockingTest(configuration: WaitConfig = MultiDispatcherWaitConfig, block: suspend TestCoroutineScope.() -> Unit) = runBlockingTest(this, configuration, block)

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
