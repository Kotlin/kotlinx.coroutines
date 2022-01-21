/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import io.reactivex.rxjava3.core.*
import io.reactivex.rxjava3.disposables.*
import io.reactivex.rxjava3.plugins.*
import kotlinx.coroutines.*
import kotlinx.coroutines.CancellationException
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

private class DispatcherScheduler(val dispatcher: CoroutineDispatcher) : Scheduler() {

    private val schedulerJob = SupervisorJob()

    /**
     * The scope for everything happening in this [DispatcherScheduler].
     *
     * Running tasks, too, get launched under this scope, because [shutdown] should cancel the running tasks as well.
     */
    private val scope = CoroutineScope(schedulerJob + dispatcher)

    override fun scheduleDirect(block: Runnable, delay: Long, unit: TimeUnit): Disposable {
        if (!scope.isActive) return Disposable.disposed()
        var handle: DisposableHandle? = null
        val task = buildTask(block) { handle!! }
        val newBlock = Runnable { scope.launch { task.block() } }
        val ctx = scope.coroutineContext
        @Suppress("INVISIBLE_MEMBER")
        ctx.delay.invokeOnTimeout(unit.toMillis(delay), newBlock, ctx).let { handle = it }
        return task
    }

    override fun createWorker(): Worker = DispatcherWorker(dispatcher, schedulerJob)

    override fun shutdown() {
        schedulerJob.cancel()
    }

    private class DispatcherWorker(dispatcher: CoroutineDispatcher, parentJob: Job) : Worker() {

        private val workerJob = SupervisorJob(parentJob)
        private val workerScope = CoroutineScope(workerJob + dispatcher)
        private val blockChannel = Channel<suspend () -> Unit>(Channel.UNLIMITED)

        init {
            workerScope.launch {
                while (isActive) {
                    val task = blockChannel.receive()
                    task()
                }
            }
        }

        override fun schedule(block: Runnable, delay: Long, unit: TimeUnit): Disposable {
            if (!workerScope.isActive) return Disposable.disposed()
            val timeMillis = unit.toMillis(delay)
            var handle: DisposableHandle? = null
            val task = buildTask(block) { handle!! }
            val newBlock = Runnable { blockChannel.trySend(task.block) }
            val ctx = workerScope.coroutineContext
            @Suppress("INVISIBLE_MEMBER")
            ctx.delay.invokeOnTimeout(timeMillis, newBlock, ctx).let { handle = it }
            return task
        }

        override fun isDisposed(): Boolean = !workerScope.isActive

        override fun dispose() {
            blockChannel.close()
            workerJob.cancel()
        }
    }

    data class Task(val disposable: Disposable, val block: suspend () -> Unit): Disposable by disposable

    companion object {
        private fun buildTask(block: Runnable, handle: () -> DisposableHandle): Task {
            val decoratedBlock = RxJavaPlugins.onSchedule(block)
            val disposable = Disposable.fromRunnable {
                handle().dispose()
            }
            return Task(disposable) {
                if (!disposable.isDisposed) {
                    try {
                        runInterruptible {
                            decoratedBlock.run()
                        }
                    } catch (e: Throwable) {
                        // TODO: what about TimeoutCancellationException?
                        if (e !is CancellationException)
                            RxJavaPlugins.onError(e)
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