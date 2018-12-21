/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import java.io.Closeable
import java.util.concurrent.*
import kotlin.coroutines.*

/**
 * [CoroutineDispatcher] that has underlying [Executor] for dispatching tasks.
 * Instances of [ExecutorCoroutineDispatcher] should be closed by the owner of the dispatcher.
 *
 * This class is generally used as a bridge between coroutine-based API and
 * asynchronous API which requires instance of the [Executor].
 */
public abstract class ExecutorCoroutineDispatcher: CoroutineDispatcher(), Closeable {
    /**
     * Closes this coroutine dispatcher and shuts down its executor.
     *
     * It may throw an exception if this dispatcher is global and cannot be closed.
     */
    public abstract override fun close()

    /**
     * Underlying executor of current [CoroutineDispatcher].
     */
    public abstract val executor: Executor
}

/**
 * Converts an instance of [ExecutorService] to an implementation of [ExecutorCoroutineDispatcher].
 */
@JvmName("from") // this is for a nice Java API, see issue #255
public fun ExecutorService.asCoroutineDispatcher(): ExecutorCoroutineDispatcher =
    // we know that an implementation of Executor.asCoroutineDispatcher actually returns a closeable one
    (this as Executor).asCoroutineDispatcher() as ExecutorCoroutineDispatcher

/**
 * Converts an instance of [Executor] to an implementation of [CoroutineDispatcher].
 */
@JvmName("from") // this is for a nice Java API, see issue #255
public fun Executor.asCoroutineDispatcher(): CoroutineDispatcher =
    ExecutorCoroutineDispatcherImpl(this)

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
            executor.execute(timeSource.wrapTask(block))
        } catch (e: RejectedExecutionException) {
            timeSource.unTrackTask()
            DefaultExecutor.enqueue(block)
        }
    }

    /*
     * removesFutureOnCancellation is required to avoid memory leak.
     * On Java 7+ we reflectively invoke ScheduledThreadPoolExecutor.setRemoveOnCancelPolicy(true) and we're fine.
     * On Java 6 we're scheduling time-based coroutines to our own thread safe heap which supports cancellation.
     */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val future = if (removesFutureOnCancellation) {
            scheduleBlock(ResumeUndispatchedRunnable(this, continuation), timeMillis, TimeUnit.MILLISECONDS)
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

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        val future = if (removesFutureOnCancellation) {
            scheduleBlock(block, timeMillis, TimeUnit.MILLISECONDS)
        } else {
            null
        }

        return if (future != null ) DisposableFutureHandle(future) else DefaultExecutor.invokeOnTimeout(timeMillis, block)
    }

    private fun scheduleBlock(block: Runnable, time: Long, unit: TimeUnit): ScheduledFuture<*>? {
        return try {
            (executor as? ScheduledExecutorService)?.schedule(block, time, unit)
        } catch (e: RejectedExecutionException) {
            null
        }
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
