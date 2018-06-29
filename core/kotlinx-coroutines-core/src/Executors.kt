/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.timeunit.TimeUnit
import java.io.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

/**
 * [CoroutineDispatcher] that implements [Closeable]
 */
abstract class CloseableCoroutineDispatcher: CoroutineDispatcher(), Closeable

/**
 * Converts an instance of [ExecutorService] to an implementation of [CloseableCoroutineDispatcher].
 */
public fun ExecutorService.asCoroutineDispatcher(): CloseableCoroutineDispatcher =
    // we know that an implementation of Executor.asCoroutineDispatcher actually returns a closeable one
    (this as Executor).asCoroutineDispatcher() as CloseableCoroutineDispatcher

/**
 * Converts an instance of [Executor] to an implementation of [CoroutineDispatcher].
 * @suppress **Deprecated**: Renamed to [asCoroutineDispatcher].
 */
@Deprecated("Renamed to `asCoroutineDispatcher`",
    replaceWith = ReplaceWith("asCoroutineDispatcher()"))
public fun Executor.toCoroutineDispatcher(): CoroutineDispatcher =
    ExecutorCoroutineDispatcher(this)

/**
 * Converts an instance of [Executor] to an implementation of [CoroutineDispatcher].
 */
public fun Executor.asCoroutineDispatcher(): CoroutineDispatcher =
    ExecutorCoroutineDispatcher(this)

private class ExecutorCoroutineDispatcher(override val executor: Executor) : ExecutorCoroutineDispatcherBase()

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
public abstract class ExecutorCoroutineDispatcherBase : CloseableCoroutineDispatcher(), Delay {
    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal abstract val executor: Executor
    
    override fun dispatch(context: CoroutineContext, block: Runnable) =
        try { executor.execute(timeSource.trackTask(block)) }
        catch (e: RejectedExecutionException) {
            timeSource.unTrackTask()
            DefaultExecutor.execute(block)
        }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val timeout =
            try { (executor as? ScheduledExecutorService)
                ?.schedule(ResumeUndispatchedRunnable(this, continuation), time, unit) }
            catch (e: RejectedExecutionException) { null }
        if (timeout != null)
            continuation.cancelFutureOnCancellation(timeout)
        else
            DefaultExecutor.scheduleResumeAfterDelay(time, unit, continuation)
    }

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle {
        val timeout =
            try { (executor as? ScheduledExecutorService)
                ?.schedule(block, time, unit) }
            catch (e: RejectedExecutionException) { null }
        if (timeout != null)
            return DisposableFutureHandle(timeout)
        else
            return DefaultExecutor.invokeOnTimeout(time, unit, block)
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
public class DisposableFutureHandle(private val future: Future<*>) : DisposableHandle {
    override fun dispose() {
        future.cancel(false)
    }
    override fun toString(): String = "DisposableFutureHandle[$future]"
}
