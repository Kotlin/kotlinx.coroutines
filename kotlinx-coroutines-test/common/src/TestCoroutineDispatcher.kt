/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * [CoroutineDispatcher] that performs both immediate and lazy execution of coroutines in tests
 * and uses a [TestCoroutineScheduler] to control its virtual clock.
 *
 * By default, [TestCoroutineDispatcher] is immediate. That means any tasks scheduled to be run without delay are
 * immediately executed. If they were scheduled with a delay, the virtual clock-time must be advanced via one of the
 * methods on the dispatcher's [scheduler].
 *
 * When switched to lazy execution using [pauseDispatcher] any coroutines started via [launch] or [async] will
 * not execute until a call to [DelayController.runCurrent] or the virtual clock-time has been advanced via one of the
 * methods on [DelayController].
 *
 * @see DelayController
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public class TestCoroutineDispatcher(
    /**
     * The scheduler that this dispatcher is linked to.
     */
    public override val scheduler: TestCoroutineScheduler = TestCoroutineScheduler()
):
    TestDispatcher(), Delay, SchedulerAsDelayController
{
    private var dispatchImmediately = true
        set(value) {
            field = value
            if (value) {
                // there may already be tasks from setup code we need to run
                scheduler.advanceUntilIdle()
            }
        }

    override fun processEvent(time: Long, marker: Any) {
        require(marker is Runnable)
        marker.run()
    }

    /** @suppress */
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        checkSchedulerInContext(scheduler, context)
        if (dispatchImmediately) {
            block.run()
        } else {
            post(block)
        }
    }

    /** @suppress */
    @InternalCoroutinesApi
    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        checkSchedulerInContext(scheduler, context)
        post(block)
    }

    /** @suppress */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        checkSchedulerInContext(scheduler, continuation.context)
        val timedRunnable = CancellableContinuationRunnable(continuation, this)
        scheduler.registerEvent(this, timeMillis, timedRunnable, ::cancellableRunnableIsCancelled)
    }

    /** @suppress */
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        checkSchedulerInContext(scheduler, context)
        return scheduler.registerEvent(this, timeMillis, block) { false }
    }

    /** @suppress */
    override fun toString(): String = "TestCoroutineDispatcher[scheduler=$scheduler]"

    private fun post(block: Runnable) =
        scheduler.registerEvent(this, 0, block) { false }

    /** @suppress */
    override suspend fun pauseDispatcher(block: suspend () -> Unit) {
        val previous = dispatchImmediately
        dispatchImmediately = false
        try {
            block()
        } finally {
            dispatchImmediately = previous
        }
    }

    /** @suppress */
    override fun pauseDispatcher() {
        dispatchImmediately = false
    }

    /** @suppress */
    override fun resumeDispatcher() {
        dispatchImmediately = true
    }
}

/**
 * This class exists to allow cleanup code to avoid throwing for cancelled continuations scheduled
 * in the future.
 */
private class CancellableContinuationRunnable(
    @JvmField val continuation: CancellableContinuation<Unit>,
    private val dispatcher: CoroutineDispatcher
) : Runnable {
    override fun run() = with(dispatcher) { with(continuation) { resumeUndispatched(Unit) } }
}

private fun cancellableRunnableIsCancelled(runnable: CancellableContinuationRunnable): Boolean =
    !runnable.continuation.isActive