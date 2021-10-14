/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * An unconfined [TestDispatcher].
 *
 * This dispatcher is similar to [Dispatchers.Unconfined]: the tasks that it executes are not confined to any particular
 * thread and form an event loop; it's different in that it skips delays, as all [TestDispatcher]s do.
 *
 * Using this [TestDispatcher] can greatly simplify writing tests where it's not important which thread is used when and
 * in which order the queued coroutines are executed. However, please be aware that, like [Dispatchers.Unconfined], this
 * is a specific dispatcher with execution order guarantees that are unusual and not shared by most other dispatchers,
 * so it can only be used reliably for testing functionality, not the specific order of actions.
 * See [Dispatchers.Unconfined] for a discussion of the execution order guarantees.
 *
 * In order to support delay skipping, this dispatcher is linked to a [TestCoroutineScheduler], which is used to control
 * the virtual time and can be shared among many test dispatchers. If no [scheduler] is passed as an argument, a new one
 * is created.
 *
 * Additionally, [name] can be set to distinguish each dispatcher instance when debugging.
 *
 * @see StandardTestDispatcher for a more predictable [TestDispatcher] that, however, requires interacting with the
 * scheduler in order for the tasks to run.
 */
@ExperimentalCoroutinesApi
public class UnconfinedTestDispatcher(
    public override val scheduler: TestCoroutineScheduler = TestCoroutineScheduler(),
    private val name: String? = null
): TestDispatcher(), Delay {

    /** @suppress */
    override fun processEvent(time: Long, marker: Any) {
        check(marker is Runnable)
        marker.run()
    }

    /** @suppress */
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = false

    /** @suppress */
    @Suppress("INVISIBLE_MEMBER")
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        checkSchedulerInContext(scheduler, context)
        scheduler.sendDispatchEvent()

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

    /** @suppress */
    override fun toString(): String = "${name ?: "UnconfinedTestDispatcher"}[scheduler=$scheduler]"

}

/**
 * A [TestDispatcher] instance whose tasks are run inside calls to the [scheduler].
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
 * If a [scheduler] is not passed as an argument, a new one is created.
 *
 * One can additionally pass a [name] in order to more easily distinguish this dispatcher during debugging.
 *
 * @see UnconfinedTestDispatcher for a dispatcher that is not confined to any particular thread.
 */
@ExperimentalCoroutinesApi
public class StandardTestDispatcher(
    public override val scheduler: TestCoroutineScheduler = TestCoroutineScheduler(),
    private val name: String? = null
): TestDispatcher(), Delay {

    /** @suppress */
    override fun processEvent(time: Long, marker: Any) {
        check(marker is Runnable)
        marker.run()
    }

    /** @suppress */
    @Suppress("INVISIBLE_MEMBER")
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        checkSchedulerInContext(scheduler, context)
        scheduler.registerEvent(this, 0, block) { false }
    }

    /** @suppress */
    override fun toString(): String = "${name ?: "ConfinedTestDispatcher"}[scheduler=$scheduler]"

}
