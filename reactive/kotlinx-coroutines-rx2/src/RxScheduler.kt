/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.Scheduler
import io.reactivex.disposables.Disposable
import io.reactivex.disposables.Disposables
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

public class DispatcherScheduler(private val dispatcher: CoroutineDispatcher) : Scheduler() {

    private val scope = CoroutineScope(SupervisorJob())

    override fun scheduleDirect(run: java.lang.Runnable): Disposable {
        val decoratedRun = RxJavaPlugins.onSchedule(run)
        val worker = createWorker()
        worker.schedule(decoratedRun)
        return worker
    }

    override fun scheduleDirect(run: java.lang.Runnable, delay: Long, unit: TimeUnit): Disposable {
        val decoratedRun = RxJavaPlugins.onSchedule(run)
        val job = scope.launch {
            try {
                delay(unit.toMillis(delay))
                if (isActive) {
                    dispatcher.dispatch(EmptyCoroutineContext, decoratedRun)
                }
            } finally {
                // do nothing
            }
        }
        return createWorker(job)
    }

    private inner class DispatcherWorker(
            private val workerJob: Job = Job(scope.coroutineContext[Job])
    ) : Worker() {
        override fun isDisposed(): Boolean = !workerJob.isActive

        override fun schedule(run: java.lang.Runnable, delay: Long, unit: TimeUnit): Disposable {
            return if (workerJob.isActive) {
                dispatcher.dispatch(EmptyCoroutineContext, run)
                return this
            } else {
                Disposables.disposed()
            }
        }

        override fun dispose() {
            workerJob.cancel()
        }
    }

    private fun createWorker(workerJob: Job) = DispatcherWorker(workerJob)

    override fun createWorker(): Worker = DispatcherWorker()

    override fun shutdown() {
        scope.cancel()
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
