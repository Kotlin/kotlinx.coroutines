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

    override fun scheduleDirect(run: java.lang.Runnable): Disposable {
        val decoratedRun = RxJavaPlugins.onSchedule(run)
        val worker = createWorker() as DispatcherWorker
        worker.schedule(decoratedRun)
        return worker
    }

    override fun scheduleDirect(run: java.lang.Runnable, delay: Long, unit: TimeUnit): Disposable {
        val decoratedRun = RxJavaPlugins.onSchedule(run)
        val worker = createWorker() as DispatcherWorker
        worker.schedule(decoratedRun, delay, unit)
        return worker
    }

    private class DispatcherWorker(private val dispatcher: CoroutineDispatcher) : Worker() {

        private val workerScope = CoroutineScope(Job())

        override fun isDisposed(): Boolean = !workerScope.isActive

        override fun schedule(run: java.lang.Runnable): Disposable {
            return if (workerScope.isActive) {
                dispatcher.dispatch(EmptyCoroutineContext, run)
                return this
            } else {
                Disposables.disposed()
            }
        }

        override fun schedule(run: java.lang.Runnable, delay: Long, unit: TimeUnit): Disposable {
            return if (delay <= 0) {
                schedule(run)
            } else {
                if (workerScope.isActive) {
                    workerScope.launch {
                        delay(unit.toMillis(delay))
                        schedule(run)
                    }
                    return this
                } else {
                    Disposables.disposed()
                }
            }
        }

        override fun dispose() {
            workerScope.cancel()
        }
    }

    override fun createWorker(): Worker = DispatcherWorker(dispatcher)
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
