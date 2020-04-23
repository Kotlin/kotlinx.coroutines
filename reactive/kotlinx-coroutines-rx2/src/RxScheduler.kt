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

    val parentJob = SupervisorJob()
    private val parentScope = CoroutineScope(parentJob)

    override fun scheduleDirect(run: java.lang.Runnable): Disposable {
        val decoratedRun = RxJavaPlugins.onSchedule(run)
        val worker = createWorker() as DispatcherWorker
        worker.startProcessingQueue(parentJob)
        worker.schedule(decoratedRun)
        return worker
    }

    override fun scheduleDirect(run: java.lang.Runnable, delay: Long, unit: TimeUnit): Disposable {
        val decoratedRun = RxJavaPlugins.onSchedule(run)
        val worker = createWorker() as DispatcherWorker
        worker.startProcessingQueue(parentJob)
        worker.schedule(decoratedRun, delay, unit)
        return worker
    }

    override fun createWorker(): Worker =
        DispatcherWorker(dispatcher)

    override fun shutdown() {
        parentScope.cancel()
    }

    private class DispatcherWorker(private val dispatcher: CoroutineDispatcher) : Worker() {

        private lateinit var workerScope: CoroutineScope
        private val blockChannel = Channel<java.lang.Runnable>()

        override fun isDisposed(): Boolean = !workerScope.isActive

        override fun schedule(block: java.lang.Runnable): Disposable =
            if (workerScope.isActive) {
                workerScope.launch(dispatcher) {
                    blockChannel.send(block)
                }
                this
            } else {
                Disposables.disposed()
            }

        override fun schedule(block: java.lang.Runnable, delay: Long, unit: TimeUnit): Disposable =
            if (delay <= 0) {
                schedule(block)
            } else {
                if (workerScope.isActive) {
                    workerScope.launch(dispatcher) {
                        delay(unit.toMillis(delay))
                        block.run()
                    }
                    this
                } else {
                    Disposables.disposed()
                }
            }

        override fun dispose() {
            workerScope.cancel()
        }

        fun startProcessingQueue(parentJob: Job) {
            workerScope = CoroutineScope(SupervisorJob(parentJob))
            workerScope.launch(dispatcher) {
                while (true) {
                    yield()
                    if (!blockChannel.isEmpty) {
                        val block = blockChannel.receive()
                        block.run()
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
