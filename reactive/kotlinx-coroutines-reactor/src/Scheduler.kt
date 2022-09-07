/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import reactor.core.Disposable
import reactor.core.scheduler.Scheduler
import java.util.concurrent.TimeUnit
import kotlin.coroutines.CoroutineContext

/**
 * Converts an instance of [Scheduler] to an implementation of [CoroutineDispatcher].
 */
public fun Scheduler.asCoroutineDispatcher(): SchedulerCoroutineDispatcher = SchedulerCoroutineDispatcher(this)

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary [Scheduler].
 * @param scheduler a scheduler.
 */
public class SchedulerCoroutineDispatcher(
    /**
     * Underlying scheduler of current [CoroutineDispatcher].
     */
    public val scheduler: Scheduler
) : CoroutineDispatcher(), AbstractDelay<Disposable> {
    /** @suppress */
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        scheduler.schedule(block)
    }

    override fun handleAsDisposable(handle: Disposable): DisposableHandle = handle.asDisposableHandle()

    override fun cancellableContinuationToRunnable(continuation: CancellableContinuation<Unit>): Runnable = Runnable {
        with(continuation) { resumeUndispatched(Unit) }
    }

    override fun schedule(timeMillis: Long, block: Runnable, context: CoroutineContext): Disposable =
        scheduler.schedule(block, timeMillis, TimeUnit.MILLISECONDS)

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
