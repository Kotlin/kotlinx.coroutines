/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * A test dispatcher that can interface with a [TestCoroutineScheduler].
 */
@ExperimentalCoroutinesApi
public abstract class TestDispatcher internal constructor(): CoroutineDispatcher(), Delay {
    /** The scheduler that this dispatcher is linked to. */
    @ExperimentalCoroutinesApi
    public abstract val scheduler: TestCoroutineScheduler

    /** Notifies the dispatcher that it should process a single event marked with [marker] happening at time [time]. */
    internal fun processEvent(time: Long, marker: Any) {
        check(marker is Runnable)
        marker.run()
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
