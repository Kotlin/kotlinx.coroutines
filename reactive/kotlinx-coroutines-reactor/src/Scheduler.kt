/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.*
import reactor.core.Disposable
import reactor.core.scheduler.Scheduler
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Converts an instance of [Scheduler] to an implementation of [CoroutineDispatcher].
 */
fun Scheduler.asCoroutineDispatcher() = SchedulerCoroutineDispatcher(this)

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary [Scheduler].
 * @param scheduler a scheduler.
 */
open class SchedulerCoroutineDispatcher(private val scheduler: Scheduler) : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        scheduler.schedule(block)
    }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val disposable = scheduler.schedule({
            with(continuation) { resumeUndispatched(Unit) }
        }, time, unit)
        continuation.disposeOnCancellation(disposable.asDisposableHandle())
    }

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle =
        scheduler.schedule(block, time, unit).asDisposableHandle()

    override fun toString(): String = scheduler.toString()
    override fun equals(other: Any?): Boolean = other is SchedulerCoroutineDispatcher && other.scheduler === scheduler
    override fun hashCode(): Int = System.identityHashCode(scheduler)
}

private fun Disposable.asDisposableHandle(): DisposableHandle =
    object : DisposableHandle {
        override fun dispose() = this@asDisposableHandle.dispose()
    }