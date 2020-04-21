/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import io.reactivex.plugins.*
import kotlinx.coroutines.*
import java.util.concurrent.*
import kotlin.coroutines.*

/**
 * Converts an instance of [Scheduler] to an implementation of [CoroutineDispatcher]
 * and provides native support of [delay] and [withTimeout].
 */
public fun Scheduler.asCoroutineDispatcher(): SchedulerCoroutineDispatcher = SchedulerCoroutineDispatcher(this)

/**
 * Converts an instance of [CoroutineDispatcher] to an implementation of [Scheduler].
 */
public fun CoroutineDispatcher.asScheduler(): Scheduler =
    if (this is SchedulerCoroutineDispatcher) {
        scheduler
    } else {
        DispatcherScheduler(this)
    }

private class DispatcherScheduler(private val dispatcher: CoroutineDispatcher) : Scheduler() {

    private val scope = CoroutineScope(SupervisorJob())

    override fun scheduleDirect(run: java.lang.Runnable): Disposable {
        val decoratedRun = RxJavaPlugins.onSchedule(run)
        val worker = createWorker() as DispatcherWorker
        worker.setJob(Job(scope.coroutineContext[Job]))
        worker.schedule(decoratedRun)
        return worker
    }

    override fun scheduleDirect(run: java.lang.Runnable, delay: Long, unit: TimeUnit): Disposable {
        val decoratedRun = RxJavaPlugins.onSchedule(run)
        val worker = createWorker() as DispatcherWorker
        val job = scope.launch {
            delay(unit.toMillis(delay))
            worker.schedule(decoratedRun)
        }
        worker.setJob(job)
        return worker
    }

    private inner class DispatcherWorker : Worker() {

        private lateinit var workerJob: Job

        fun setJob(job: Job) {
            workerJob = job
        }

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
