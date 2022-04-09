/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import io.reactivex.plugins.*
import kotlinx.atomicfu.*
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

@Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.4.2, binary compatibility with earlier versions")
@JvmName("asCoroutineDispatcher")
public fun Scheduler.asCoroutineDispatcher0(): SchedulerCoroutineDispatcher =
    SchedulerCoroutineDispatcher(this)

/**
 * Converts an instance of [CoroutineDispatcher] to an implementation of [Scheduler].
 */
public fun CoroutineDispatcher.asScheduler(): Scheduler =
    if (this is SchedulerCoroutineDispatcher) {
        scheduler
    } else {
        DispatcherScheduler(this)
    }

private class DispatcherScheduler(@JvmField val dispatcher: CoroutineDispatcher) : Scheduler() {

    private val schedulerJob = SupervisorJob()

    /**
     * The scope for everything happening in this [DispatcherScheduler].
     *
     * Running tasks, too, get launched under this scope, because [shutdown] should cancel the running tasks as well.
     */
    private val scope = CoroutineScope(schedulerJob + dispatcher)

    /**
     * The counter of created workers, for their pretty-printing.
     */
    private val workerCounter = atomic(1L)

    override fun scheduleDirect(block: Runnable, delay: Long, unit: TimeUnit): Disposable =
        scope.scheduleTask(block, unit.toMillis(delay)) { task ->
            Runnable { scope.launch { task() } }
        }

    override fun createWorker(): Worker = DispatcherWorker(workerCounter.getAndIncrement(), dispatcher, schedulerJob)

    override fun shutdown() {
        schedulerJob.cancel()
    }

    private class DispatcherWorker(
        private val counter: Long,
        private val dispatcher: CoroutineDispatcher,
        parentJob: Job
    ) : Worker() {

        private val workerJob = SupervisorJob(parentJob)
        private val workerScope = CoroutineScope(workerJob + dispatcher)
        private val blockChannel = Channel<suspend () -> Unit>(Channel.UNLIMITED)

        init {
            workerScope.launch {
                blockChannel.consumeEach {
                    it()
                }
            }
        }

        override fun schedule(block: Runnable, delay: Long, unit: TimeUnit): Disposable =
            workerScope.scheduleTask(block, unit.toMillis(delay)) { task ->
                Runnable { blockChannel.trySend(task) }
            }

        override fun isDisposed(): Boolean = !workerScope.isActive

        override fun dispose() {
            blockChannel.close()
            workerJob.cancel()
        }

        override fun toString(): String = "$dispatcher (worker $counter, ${if (isDisposed) "disposed" else "active"})"
    }

    override fun toString(): String = dispatcher.toString()
}

private typealias Task = suspend () -> Unit

/**
 * Schedule [block] so that an adapted version of it, wrapped in [adaptForScheduling], executes after [delayMillis]
 * milliseconds.
 */
private fun CoroutineScope.scheduleTask(
    block: Runnable,
    delayMillis: Long,
    adaptForScheduling: (Task) -> Runnable
): Disposable {
    val ctx = coroutineContext
    var handle: DisposableHandle? = null
    val disposable = Disposables.fromRunnable {
        // null if delay <= 0
        handle?.dispose()
    }
    val decoratedBlock = RxJavaPlugins.onSchedule(block)
    suspend fun task() {
        if (disposable.isDisposed) return
        try {
            runInterruptible {
                decoratedBlock.run()
            }
        } catch (e: Throwable) {
            handleUndeliverableException(e, ctx)
        }
    }

    val toSchedule = adaptForScheduling(::task)
    if (!isActive) return Disposables.disposed()
    if (delayMillis <= 0) {
        toSchedule.run()
    } else {
        @Suppress("INVISIBLE_MEMBER")
        ctx.delay.invokeOnTimeout(delayMillis, toSchedule, ctx).let { handle = it }
    }
    return disposable
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