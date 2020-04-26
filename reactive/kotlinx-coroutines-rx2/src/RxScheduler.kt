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
    private val scope = CoroutineScope(job + dispatcher)

    override fun scheduleDirect(block: Runnable): Disposable {
        if (scope.isActive) {
            return scope.launch {
                block.runWithRx()
            }.asDisposable()
        }

        return Disposables.disposed()
    }

    override fun scheduleDirect(block: Runnable, delay: Long, unit: TimeUnit): Disposable {
        if (delay <= 0) {
            return scheduleDirect(block)
        }

        if (scope.isActive) {
            return scope.launch {
                delay(unit.toMillis(delay))
                block.runWithRx()
            }.asDisposable()
        }

        return Disposables.disposed()
    }

    private fun Runnable.runWithRx() = RxJavaPlugins.onSchedule(this).run()

    override fun createWorker(): Worker =
        DispatcherWorker(dispatcher, job)

    override fun shutdown() {
        scope.cancel()
    }

    private class DispatcherWorker(dispatcher: CoroutineDispatcher, parentJob: Job) : Worker() {

        private val workerScope = CoroutineScope(SupervisorJob(parentJob) + dispatcher)
        private val blockChannel = Channel<Job>(Channel.UNLIMITED)
        private var queueProcessingJob: Job? = null

        override fun isDisposed(): Boolean = !workerScope.isActive

        override fun schedule(block: Runnable): Disposable {
            startProcessingQueue()
            if (workerScope.isActive) {
                val job = workerScope.launch(start = CoroutineStart.LAZY) {
                    block.run()
                }
                blockChannel.offer(job)
                return job.asDisposable()
            }

            return Disposables.disposed()
        }

        override fun schedule(block: Runnable, delay: Long, unit: TimeUnit): Disposable {
            startProcessingQueue()
            if (delay <= 0) {
                return schedule(block)
            }
            if (workerScope.isActive) {
                return workerScope.launch {
                    delay(unit.toMillis(delay))
                    block.run()
                }.asDisposable()
            }
            return Disposables.disposed()
        }

        override fun dispose() {
            workerScope.cancel()
            blockChannel.close()
        }

        private fun startProcessingQueue() {
            if (queueProcessingJob == null) {
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
    override fun isDisposed(): Boolean = !job.isActive

    override fun dispose() {
        job.cancel()
    }
}

public fun Job.asDisposable(): Disposable = JobDisposable(this)
