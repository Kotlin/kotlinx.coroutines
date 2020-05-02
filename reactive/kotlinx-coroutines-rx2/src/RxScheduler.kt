/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import io.reactivex.plugins.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import java.util.concurrent.*
import kotlin.coroutines.*

/**
 * Converts an instance of [Scheduler] to an implementation of [CoroutineDispatcher]
 * and provides native support of [delay] and [withTimeout].
 */
public fun Scheduler.asCoroutineDispatcher(): CoroutineDispatcher =
    if (this is DispatcherScheduler) {
        dispatcher
    } else {
        SchedulerCoroutineDispatcher(this)
    }

/**
 * Converts an instance of [CoroutineDispatcher] to an implementation of [Scheduler].
 */
public fun CoroutineDispatcher.asScheduler(): Scheduler =
    if (this is SchedulerCoroutineDispatcher) {
        scheduler
    } else {
        DispatcherScheduler(this)
    }

private class DispatcherScheduler(internal val dispatcher: CoroutineDispatcher) : Scheduler() {

    private val job = SupervisorJob()
    private val scope = CoroutineScope(job + dispatcher + CoroutineExceptionHandler { _, throwable ->
        RxJavaPlugins.onError(throwable)
    })

    override fun scheduleDirect(block: Runnable): Disposable =
        scheduleDirect(block, 0, TimeUnit.MILLISECONDS)

    override fun scheduleDirect(block: Runnable, delay: Long, unit: TimeUnit): Disposable {
        if (!scope.isActive) return Disposables.disposed()
        return scope.launch {
            val newBlock = RxJavaPlugins.onSchedule(block)
            if (delay > 0) {
                delay(unit.toMillis(delay))
            }
            newBlock.run()
        }.asDisposable()
    }

    override fun createWorker(): Worker =
        DispatcherWorker(dispatcher, job)

    override fun shutdown() {
        scope.cancel()
    }

    private class DispatcherWorker(dispatcher: CoroutineDispatcher, parentJob: Job) : Worker() {

        private val workerScope = CoroutineScope(SupervisorJob(parentJob) + dispatcher)
        private val blockChannel = Channel<Job>(Channel.UNLIMITED)
        private var queueProcessingJob: Job? = null

        init {
            queueProcessingJob = workerScope.launch {
                while (isActive) {
                    val job = blockChannel.receive()
                    if (!job.isCancelled) {
                        job.start()
                        job.join()
                    }
                }
            }
        }

        override fun isDisposed(): Boolean = !workerScope.isActive

        override fun schedule(block: Runnable): Disposable =
            schedule(block, 0, TimeUnit.MILLISECONDS)

        override fun schedule(block: Runnable, delay: Long, unit: TimeUnit): Disposable {
            if (!workerScope.isActive) return Disposables.disposed()

            val newBlock = RxJavaPlugins.onSchedule(block)
            /*
                Start job as lazy because we're going to put the job on a Channel to be executed later.
                The client may cancel the job while it's in the queue so it's start it lazy and start job
                when it's popped off (and not cancelled).
             */
            val job = workerScope.launch(start = CoroutineStart.LAZY) {
                if (delay > 0L) {
                    delay(unit.toMillis(delay))
                }
                newBlock.run()
            }
            blockChannel.offer(job)
            return job.asDisposable()
        }

        override fun dispose() {
            workerScope.cancel()
            blockChannel.close()
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

private class JobDisposable(private val job: Job) : Disposable {
    override fun isDisposed(): Boolean = job.isCancelled || job.isCompleted

    override fun dispose() {
        job.cancel()
    }
}

private fun Job.asDisposable(): Disposable = JobDisposable(this)
