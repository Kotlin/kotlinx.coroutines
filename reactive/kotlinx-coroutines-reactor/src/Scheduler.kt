/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.*
import reactor.core.Disposable
import reactor.core.scheduler.Scheduler
import java.util.concurrent.*
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Converts an instance of [Scheduler] to an implementation of [CoroutineDispatcher].
 */
fun Scheduler.asCoroutineDispatcher(): SchedulerCoroutineDispatcher = SchedulerCoroutineDispatcher(this)

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary [Scheduler].
 * @param scheduler a scheduler.
 */
public class SchedulerCoroutineDispatcher(
    /**
     * Underlying scheduler of current [CoroutineDispatcher].
     */
    public val scheduler: Scheduler
) : CoroutineDispatcher(), Delay {
    /** @suppress */
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        scheduler.schedule(block)
    }

    /** @suppress */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val disposable = scheduler.schedule({
            with(continuation) { resumeUndispatched(Unit) }
        }, timeMillis, TimeUnit.MILLISECONDS)
        continuation.disposeOnCancellation(disposable.asDisposableHandle())
    }

    /** @suppress */
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle =
        scheduler.schedule(block, timeMillis, TimeUnit.MILLISECONDS).asDisposableHandle()

    /** @suppress */
    override fun toString(): String = scheduler.toString()
    /** @suppress */
    override fun equals(other: Any?): Boolean = other is SchedulerCoroutineDispatcher && other.scheduler === scheduler
    /** @suppress */
    override fun hashCode(): Int = System.identityHashCode(scheduler)
}

private fun Disposable.asDisposableHandle(): DisposableHandle =
    object : DisposableHandle {
        override fun dispose() = this@asDisposableHandle.dispose()
    }