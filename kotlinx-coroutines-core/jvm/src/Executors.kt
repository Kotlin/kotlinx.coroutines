/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

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

/**
 * Converts an instance of [ExecutorService] to an implementation of [ExecutorCoroutineDispatcher].
 *
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

private class ExecutorCoroutineDispatcherImpl(override val executor: Executor) : ExecutorCoroutineDispatcherBase() {
    init {
        initFutureCancellation()
    }
}

internal abstract class ExecutorCoroutineDispatcherBase : ExecutorCoroutineDispatcher(), Delay {

    private var removesFutureOnCancellation: Boolean = false

    internal fun initFutureCancellation() {
        removesFutureOnCancellation = removeFutureOnCancel(executor)
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

    /*
     * removesFutureOnCancellation is required to avoid memory leak.
     * On Java 7+ we reflectively invoke ScheduledThreadPoolExecutor.setRemoveOnCancelPolicy(true) and we're fine.
     * On Java 6 we're scheduling time-based coroutines to our own thread safe heap which supports cancellation.
     */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val future = if (removesFutureOnCancellation) {
            scheduleBlock(ResumeUndispatchedRunnable(this, continuation), continuation.context, timeMillis)
        } else {
            null
        }
        // If everything went fine and the scheduling attempt was not rejected -- use it
        if (future != null) {
            continuation.cancelFutureOnCancellation(future)
            return
        }
        // Otherwise fallback to default executor
        DefaultExecutor.scheduleResumeAfterDelay(timeMillis, continuation)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val future = if (removesFutureOnCancellation) {
            scheduleBlock(block, context, timeMillis)
        } else {
            null
        }
        return when {
            future != null -> DisposableFutureHandle(future)
            else -> DefaultExecutor.invokeOnTimeout(timeMillis, block, context)
        }
    }

    private fun scheduleBlock(block: Runnable, context: CoroutineContext, timeMillis: Long): ScheduledFuture<*>? {
        return try {
            (executor as? ScheduledExecutorService)?.schedule(block, timeMillis, TimeUnit.MILLISECONDS)
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
    override fun equals(other: Any?): Boolean = other is ExecutorCoroutineDispatcherBase && other.executor === executor
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
