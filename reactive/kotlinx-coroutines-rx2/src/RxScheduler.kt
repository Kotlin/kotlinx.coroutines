/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.Scheduler
import io.reactivex.disposables.Disposable
import io.reactivex.plugins.RxJavaPlugins
import kotlinx.coroutines.*
import java.util.concurrent.TimeUnit
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

/**
 * Converts an instance of [Scheduler] to an implementation of [CoroutineDispatcher]
 * and provides native support of [delay] and [withTimeout].
 */
public fun Scheduler.asCoroutineDispatcher(): SchedulerCoroutineDispatcher = SchedulerCoroutineDispatcher(this)

public fun CoroutineDispatcher.asScheduler(): Scheduler =
        if (this is SchedulerCoroutineDispatcher) {
            scheduler
        } else {
            // what do we do in this case?
            DispatcherScheduler(this)
        }

public class DispatcherScheduler(public val dispatcher: CoroutineDispatcher) : Scheduler() {

    private val scope = CoroutineScope(EmptyCoroutineContext)

    override fun createWorker(): Worker {
        return object : Worker() {
            override fun isDisposed(): Boolean = !scope.isActive

            override fun schedule(run: java.lang.Runnable, delay: Long, unit: TimeUnit): Disposable {
                RxJavaPlugins.onSchedule(run)
                if (scope.isActive) {
                    if (delay <= 0) {
                        dispatcher.dispatch(EmptyCoroutineContext, run)
                    } else {
                        scope.launch {
                            try {
                                delay(unit.toMillis(delay))
                                dispatcher.dispatch(EmptyCoroutineContext, run)
                            } finally {
                                // do nothing
                            }
                        }
                    }
                }

                return this
            }

            override fun dispose() {
                scope.cancel()
            }
        }
    }
}

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary [Scheduler].
 */
public class SchedulerCoroutineDispatcher(
        /**
         * Underlying scheduler of current [CoroutineDispatcher].
         */
        public val scheduler: Scheduler
) : CoroutineDispatcher(), Delay {
    /** @suppress */
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        scheduler.scheduleDirect(block)
    }

    /** @suppress */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val disposable = scheduler.scheduleDirect({
            with(continuation) { resumeUndispatched(Unit) }
        }, timeMillis, TimeUnit.MILLISECONDS)
        continuation.disposeOnCancellation(disposable)
    }

    /** @suppress */
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val disposable = scheduler.scheduleDirect(block, timeMillis, TimeUnit.MILLISECONDS)
        return DisposableHandle { disposable.dispose() }
    }

    /** @suppress */
    override fun toString(): String = scheduler.toString()

    /** @suppress */
    override fun equals(other: Any?): Boolean = other is SchedulerCoroutineDispatcher && other.scheduler === scheduler

    /** @suppress */
    override fun hashCode(): Int = System.identityHashCode(scheduler)
}
