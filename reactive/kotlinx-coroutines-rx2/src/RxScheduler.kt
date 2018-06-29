/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.Scheduler
import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.CoroutineDispatcher
import kotlinx.coroutines.experimental.Delay
import kotlinx.coroutines.experimental.DisposableHandle
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Converts an instance of [Scheduler] to an implementation of [CoroutineDispatcher]
 * and provides native [delay][Delay.delay] support.
 */
public fun Scheduler.asCoroutineDispatcher() = SchedulerCoroutineDispatcher(this)

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary [Scheduler].
 * @param scheduler a scheduler.
 */
public class SchedulerCoroutineDispatcher(private val scheduler: Scheduler) : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        scheduler.scheduleDirect(block)
    }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val disposable = scheduler.scheduleDirect({
            with(continuation) { resumeUndispatched(Unit) }
        }, time, unit)
        continuation.disposeOnCancellation(disposable)
    }

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle {
        val disposable = scheduler.scheduleDirect(block, time, unit)
        return object : DisposableHandle {
            override fun dispose() {
                disposable.dispose()
            }
        }
    }

    override fun toString(): String = scheduler.toString()
    override fun equals(other: Any?): Boolean = other is SchedulerCoroutineDispatcher && other.scheduler === scheduler
    override fun hashCode(): Int = System.identityHashCode(scheduler)
}
