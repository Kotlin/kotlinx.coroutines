/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlin.time.*

/**
 * A test dispatcher that can interface with a [TestCoroutineScheduler].
 *
 * The available implementations are:
 * * [StandardTestDispatcher] is a dispatcher that places new tasks into a queue.
 * * [UnconfinedTestDispatcher] is a dispatcher that behaves like [Dispatchers.Unconfined] while allowing to control
 *   the virtual time.
 */
@Suppress("INVISIBLE_REFERENCE")
public abstract class TestDispatcher internal constructor() : CoroutineDispatcher(), Delay, DelayWithTimeoutDiagnostics {
    /** The scheduler that this dispatcher is linked to. */
    public abstract val scheduler: TestCoroutineScheduler

    /** Notifies the dispatcher that it should process a single event marked with [marker] happening at time [time]. */
    internal fun processEvent(marker: Any) {
        check(marker is Runnable)
        marker.run()
    }

    /** @suppress */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val timedRunnable = CancellableContinuationRunnable(continuation, this)
        val handle = scheduler.registerEvent(
            this,
            timeMillis,
            timedRunnable,
            continuation.context,
            ::cancellableRunnableIsCancelled
        )
        continuation.disposeOnCancellation(handle)
    }

    /** @suppress */
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        scheduler.registerEvent(this, timeMillis, block, context) { false }

    /** @suppress */
    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    @Deprecated("Is only needed internally", level = DeprecationLevel.HIDDEN)
    public override fun timeoutMessage(timeout: Duration): String =
        "Timed out after $timeout of _virtual_ (kotlinx.coroutines.test) time. " +
            "To use the real time, wrap 'withTimeout' in 'withContext(Dispatchers.Default.limitedParallelism(1))'"
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
