/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.test.internal.TestMainDispatcher
import kotlin.coroutines.*

/**
 * Creates an instance of an unconfined [TestDispatcher].
 *
 * This dispatcher is similar to [Dispatchers.Unconfined]: the tasks that it executes are not confined to any particular
 * thread and form an event loop; it's different in that it skips delays, as all [TestDispatcher]s do.
 *
 * Like [Dispatchers.Unconfined], this one does not provide guarantees about the execution order when several coroutines
 * are queued in this dispatcher. However, we ensure that the [launch] and [async] blocks at the top level of [runTest]
 * are entered eagerly. This allows launching child coroutines and not calling [runCurrent] for them to start executing.
 *
 * ```
 * @Test
 * fun testEagerlyEnteringChildCoroutines() = runTest(UnconfinedTestDispatcher()) {
 *   var entered = false
 *   val deferred = CompletableDeferred<Unit>()
 *   var completed = false
 *   launch {
 *     entered = true
 *     deferred.await()
 *     completed = true
 *   }
 *   assertTrue(entered) // `entered = true` already executed.
 *   assertFalse(completed) // however, the child coroutine then suspended, so it is enqueued.
 *   deferred.complete(Unit) // resume the coroutine.
 *   assertTrue(completed) // now the child coroutine is immediately completed.
 * }
 * ```
 *
 * Using this [TestDispatcher] can greatly simplify writing tests where it's not important which thread is used when and
 * in which order the queued coroutines are executed.
 * Another typical use case for this dispatcher is launching child coroutines that are resumed immediately, without
 * going through a dispatch; this can be helpful for testing [Channel] and [StateFlow] usages.
 *
 * ```
 * @Test
 * fun testUnconfinedDispatcher() = runTest {
 *   val values = mutableListOf<Int>()
 *   val stateFlow = MutableStateFlow(0)
 *   val job = launch(UnconfinedTestDispatcher(testScheduler)) {
 *     stateFlow.collect {
 *       values.add(it)
 *     }
 *   }
 *   stateFlow.value = 1
 *   stateFlow.value = 2
 *   stateFlow.value = 3
 *   job.cancel()
 *   // each assignment will immediately resume the collecting child coroutine,
 *   // so no values will be skipped.
 *   assertEquals(listOf(0, 1, 2, 3), values)
 * }
 * ```
 *
 * Please be aware that, like [Dispatchers.Unconfined], this is a specific dispatcher with execution order
 * guarantees that are unusual and not shared by most other dispatchers, so it can only be used reliably for testing
 * functionality, not the specific order of actions.
 * See [Dispatchers.Unconfined] for a discussion of the execution order guarantees.
 *
 * In order to support delay skipping, this dispatcher is linked to a [TestCoroutineScheduler], which is used to control
 * the virtual time and can be shared among many test dispatchers.
 * If no [scheduler] is passed as an argument, [Dispatchers.Main] is checked, and if it was mocked with a
 * [TestDispatcher] via [Dispatchers.setMain], the [TestDispatcher.scheduler] of the mock dispatcher is used; if
 * [Dispatchers.Main] is not mocked with a [TestDispatcher], a new [TestCoroutineScheduler] is created.
 *
 * Additionally, [name] can be set to distinguish each dispatcher instance when debugging.
 *
 * @see StandardTestDispatcher for a more predictable [TestDispatcher].
 */
@ExperimentalCoroutinesApi
@Suppress("FunctionName")
public fun UnconfinedTestDispatcher(
    scheduler: TestCoroutineScheduler? = null,
    name: String? = null
): TestDispatcher = UnconfinedTestDispatcherImpl(
    scheduler ?: TestMainDispatcher.currentTestScheduler ?: TestCoroutineScheduler(), name)

private class UnconfinedTestDispatcherImpl(
    override val scheduler: TestCoroutineScheduler,
    private val name: String? = null
) : TestDispatcher() {

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = false

    @Suppress("INVISIBLE_MEMBER")
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        checkSchedulerInContext(scheduler, context)
        scheduler.sendDispatchEvent(context)

        /** copy-pasted from [kotlinx.coroutines.Unconfined.dispatch] */
        /** It can only be called by the [yield] function. See also code of [yield] function. */
        val yieldContext = context[YieldContext]
        if (yieldContext !== null) {
            // report to "yield" that it is an unconfined dispatcher and don't call "block.run()"
            yieldContext.dispatcherWasUnconfined = true
            return
        }
        throw UnsupportedOperationException(
            "Function UnconfinedTestCoroutineDispatcher.dispatch can only be used by " +
                "the yield function. If you wrap Unconfined dispatcher in your code, make sure you properly delegate " +
                "isDispatchNeeded and dispatch calls."
        )
    }

    override fun toString(): String = "${name ?: "UnconfinedTestDispatcher"}[scheduler=$scheduler]"
}

/**
 * Creates an instance of a [TestDispatcher] whose tasks are run inside calls to the [scheduler].
 *
 * This [TestDispatcher] instance does not itself execute any of the tasks. Instead, it always sends them to its
 * [scheduler], which can then be accessed via [TestCoroutineScheduler.runCurrent],
 * [TestCoroutineScheduler.advanceUntilIdle], or [TestCoroutineScheduler.advanceTimeBy], which will then execute these
 * tasks in a blocking manner.
 *
 * In practice, this means that [launch] or [async] blocks will not be entered immediately (unless they are
 * parameterized with [CoroutineStart.UNDISPATCHED]), and one should either call [TestCoroutineScheduler.runCurrent] to
 * run these pending tasks, which will block until there are no more tasks scheduled at this point in time, or, when
 * inside [runTest], call [yield] to yield the (only) thread used by [runTest] to the newly-launched coroutines.
 *
 * If no [scheduler] is passed as an argument, [Dispatchers.Main] is checked, and if it was mocked with a
 * [TestDispatcher] via [Dispatchers.setMain], the [TestDispatcher.scheduler] of the mock dispatcher is used; if
 * [Dispatchers.Main] is not mocked with a [TestDispatcher], a new [TestCoroutineScheduler] is created.
 *
 * One can additionally pass a [name] in order to more easily distinguish this dispatcher during debugging.
 *
 * @see UnconfinedTestDispatcher for a dispatcher that is not confined to any particular thread.
 */
@Suppress("FunctionName")
public fun StandardTestDispatcher(
    scheduler: TestCoroutineScheduler? = null,
    name: String? = null
): TestDispatcher = StandardTestDispatcherImpl(
    scheduler ?: TestMainDispatcher.currentTestScheduler ?: TestCoroutineScheduler(), name)

private class StandardTestDispatcherImpl(
    override val scheduler: TestCoroutineScheduler = TestCoroutineScheduler(),
    private val name: String? = null
) : TestDispatcher() {

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        scheduler.registerEvent(this, 0, block, context) { false }
    }

    override fun toString(): String = "${name ?: "StandardTestDispatcher"}[scheduler=$scheduler]"
}
