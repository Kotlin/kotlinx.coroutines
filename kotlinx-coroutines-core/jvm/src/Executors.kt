/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import java.io.*
import java.util.concurrent.*
import kotlin.coroutines.*

/**
 * [CoroutineDispatcher] that has underlying [Executor] for dispatching tasks.
 * Instances of [ExecutorCoroutineDispatcher] should be closed by the owner of the dispatcher.
 *
 * This class is generally used as a bridge between coroutine-based API and
 * asynchronous API that requires an instance of the [Executor].
 */
public abstract class ExecutorCoroutineDispatcher: CoroutineDispatcher(), Closeable {
    /** @suppress */
    @ExperimentalStdlibApi
    public companion object Key : AbstractCoroutineContextKey<CoroutineDispatcher, ExecutorCoroutineDispatcher>(
        CoroutineDispatcher,
        { it as? ExecutorCoroutineDispatcher })

    /**
     * Underlying executor of current [CoroutineDispatcher].
     */
    public abstract val executor: Executor

    /**
     * Closes this coroutine dispatcher and shuts down its executor.
     *
     * It may throw an exception if this dispatcher is global and cannot be closed.
     */
    public abstract override fun close()
}

@ExperimentalCoroutinesApi
public actual typealias CloseableCoroutineDispatcher = ExecutorCoroutineDispatcher

/**
 * Converts an instance of [ExecutorService] to an implementation of [ExecutorCoroutineDispatcher].
 *
 * ## Interaction with [delay] and time-based coroutines.
 *
 * If the given [ExecutorService] is an instance of [ScheduledExecutorService], then all time-related
 * coroutine operations such as [delay], [withTimeout] and time-based [Flow] operators will be scheduled
 * on this executor using [schedule][ScheduledExecutorService.schedule] method. If the corresponding
 * coroutine is cancelled, [ScheduledFuture.cancel] will be invoked on the corresponding future.
 *
 * If the given [ExecutorService] is an instance of [ScheduledThreadPoolExecutor], then prior to any scheduling,
 * remove on cancel policy will be set via [ScheduledThreadPoolExecutor.setRemoveOnCancelPolicy] in order
 * to reduce the memory pressure of cancelled coroutines.
 *
 * If the executor service is neither of this types, the separate internal thread will be used to
 * _track_ the delay and time-related executions, but the coroutine itself will still be executed
 * on top of the given executor.
 *
 * ## Rejected execution
 * If the underlying executor throws [RejectedExecutionException] on
 * attempt to submit a continuation task (it happens when [closing][ExecutorCoroutineDispatcher.close] the
 * resulting dispatcher, on underlying executor [shutdown][ExecutorService.shutdown], or when it uses limited queues),
 * then the [Job] of the affected task is [cancelled][Job.cancel] and the task is submitted to the
 * [Dispatchers.IO], so that the affected coroutine can cleanup its resources and promptly complete.
 */
@JvmName("from") // this is for a nice Java API, see issue #255
public fun ExecutorService.asCoroutineDispatcher(): ExecutorCoroutineDispatcher =
    ExecutorCoroutineDispatcherImpl(this)

/**
 * Converts an instance of [Executor] to an implementation of [CoroutineDispatcher].
 *
 * ## Interaction with [delay] and time-based coroutines.
 *
 * If the given [Executor] is an instance of [ScheduledExecutorService], then all time-related
 * coroutine operations such as [delay], [withTimeout] and time-based [Flow] operators will be scheduled
 * on this executor using [schedule][ScheduledExecutorService.schedule] method. If the corresponding
 * coroutine is cancelled, [ScheduledFuture.cancel] will be invoked on the corresponding future.
 *
 * If the given [Executor] is an instance of [ScheduledThreadPoolExecutor], then prior to any scheduling,
 * remove on cancel policy will be set via [ScheduledThreadPoolExecutor.setRemoveOnCancelPolicy] in order
 * to reduce the memory pressure of cancelled coroutines.
 *
 * If the executor is neither of this types, the separate internal thread will be used to
 * _track_ the delay and time-related executions, but the coroutine itself will still be executed
 * on top of the given executor.
 *
 * ## Rejected execution
 *
 * If the underlying executor throws [RejectedExecutionException] on
 * attempt to submit a continuation task (it happens when [closing][ExecutorCoroutineDispatcher.close] the
 * resulting dispatcher, on underlying executor [shutdown][ExecutorService.shutdown], or when it uses limited queues),
 * then the [Job] of the affected task is [cancelled][Job.cancel] and the task is submitted to the
 * [Dispatchers.IO], so that the affected coroutine can cleanup its resources and promptly complete.
 */
@JvmName("from") // this is for a nice Java API, see issue #255
public fun Executor.asCoroutineDispatcher(): CoroutineDispatcher =
    (this as? DispatcherExecutor)?.dispatcher ?: ExecutorCoroutineDispatcherImpl(this)

/**
 * Converts an instance of [CoroutineDispatcher] to an implementation of [Executor].
 *
 * It returns the original executor when used on the result of [Executor.asCoroutineDispatcher] extensions.
 */
public fun CoroutineDispatcher.asExecutor(): Executor =
    (this as? ExecutorCoroutineDispatcher)?.executor ?: DispatcherExecutor(this)

private class DispatcherExecutor(@JvmField val dispatcher: CoroutineDispatcher) : Executor {
    override fun execute(block: Runnable) = dispatcher.dispatch(EmptyCoroutineContext, block)
    override fun toString(): String = dispatcher.toString()
}

internal class ExecutorCoroutineDispatcherImpl(override val executor: Executor) : ExecutorCoroutineDispatcher(), Delay {

    /*
     * Attempts to reflectively (to be Java 6 compatible) invoke
     * ScheduledThreadPoolExecutor.setRemoveOnCancelPolicy in order to cleanup
     * internal scheduler queue on cancellation.
     */
    init {
        removeFutureOnCancel(executor)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        try {
            executor.execute(wrapTask(block))
        } catch (e: RejectedExecutionException) {
            unTrackTask()
            cancelJobOnRejection(context, e)
            Dispatchers.IO.dispatch(context, block)
        }
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val future = (executor as? ScheduledExecutorService)?.scheduleBlock(
            ResumeUndispatchedRunnable(this, continuation),
            continuation.context,
            timeMillis
        )
        // If everything went fine and the scheduling attempt was not rejected -- use it
        if (future != null) {
            continuation.cancelFutureOnCancellation(future)
            return
        }
        // Otherwise fallback to default executor
        DefaultExecutor.scheduleResumeAfterDelay(timeMillis, continuation)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val future = (executor as? ScheduledExecutorService)?.scheduleBlock(block, context, timeMillis)
        return when {
            future != null -> DisposableFutureHandle(future)
            else -> DefaultExecutor.invokeOnTimeout(timeMillis, block, context)
        }
    }

    private fun ScheduledExecutorService.scheduleBlock(block: Runnable, context: CoroutineContext, timeMillis: Long): ScheduledFuture<*>? {
        return try {
            schedule(block, timeMillis, TimeUnit.MILLISECONDS)
        } catch (e: RejectedExecutionException) {
            cancelJobOnRejection(context, e)
            null
        }
    }

    private fun cancelJobOnRejection(context: CoroutineContext, exception: RejectedExecutionException) {
        context.cancel(CancellationException("The task was rejected", exception))
    }

    override fun close() {
        (executor as? ExecutorService)?.shutdown()
    }

    override fun toString(): String = executor.toString()
    override fun equals(other: Any?): Boolean = other is ExecutorCoroutineDispatcherImpl && other.executor === executor
    override fun hashCode(): Int = System.identityHashCode(executor)
}

private class ResumeUndispatchedRunnable(
    private val dispatcher: CoroutineDispatcher,
    private val continuation: CancellableContinuation<Unit>
) : Runnable {
    override fun run() {
        with(continuation) { dispatcher.resumeUndispatched(Unit) }
    }
}

/**
 * An implementation of [DisposableHandle] that cancels the specified future on dispose.
 * @suppress **This is unstable API and it is subject to change.**
 */
private class DisposableFutureHandle(private val future: Future<*>) : DisposableHandle {
    override fun dispose() {
        future.cancel(false)
    }
    override fun toString(): String = "DisposableFutureHandle[$future]"
}
