/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import java.io.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

/**
 * [CoroutineDispatcher] that has underlying [Executor] for dispatching tasks.
 * Instances of [ExecutorCoroutineDispatcher] should be closed by the owner of the dispatcher.
 *
 * This class is generally used as a bridge between coroutine-based API and
 * asynchronous API which requires instance of the [Executor].
 */
public abstract class ExecutorCoroutineDispatcher: CloseableCoroutineDispatcher(), Closeable {
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
 * [CoroutineDispatcher] that implements [Closeable].
 *
 * @suppress **Deprecated**: Use [ExecutorCoroutineDispatcher].
 */
@Deprecated("Use ExecutorCoroutineDispatcher instead", replaceWith = ReplaceWith("ExecutorCoroutineDispatcher"))
public abstract class CloseableCoroutineDispatcher: CoroutineDispatcher(), Closeable

/**
 * Converts an instance of [ExecutorService] to an implementation of [ExecutorCoroutineDispatcher].
 */
public fun ExecutorService.asCoroutineDispatcher(): ExecutorCoroutineDispatcher =
    // we know that an implementation of Executor.asCoroutineDispatcher actually returns a closeable one
    (this as Executor).asCoroutineDispatcher() as ExecutorCoroutineDispatcher

/**
 * Converts an instance of [Executor] to an implementation of [CoroutineDispatcher].
 */
@JvmName("from") // this is for a nice Java API, see issue #255
public fun Executor.asCoroutineDispatcher(): CoroutineDispatcher =
    ExecutorCoroutineDispatcherImpl(this)

/**
 * Converts an instance of [ExecutorService] to an implementation of [CloseableCoroutineDispatcher].
 * @suppress **Deprecated**: Return type changed to [ExecutorCoroutineDispatcher].
 */
@Deprecated(level = DeprecationLevel.HIDDEN, message = "Return type changed to ExecutorCoroutineDispatcher")
@JvmName("asCoroutineDispatcher") // for binary compatibility
public fun ExecutorService.asCoroutineDispatcher_Deprecated(): CloseableCoroutineDispatcher =
    asCoroutineDispatcher()

/**
 * Converts an instance of [Executor] to an implementation of [CoroutineDispatcher].
 * @suppress **Deprecated**: Renamed to [asCoroutineDispatcher].
 */
@Deprecated("Renamed to `asCoroutineDispatcher`",
    replaceWith = ReplaceWith("asCoroutineDispatcher()"))
public fun Executor.toCoroutineDispatcher(): CoroutineDispatcher =
    asCoroutineDispatcher()

private class ExecutorCoroutineDispatcherImpl(override val executor: Executor) : ExecutorCoroutineDispatcherBase()

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
@InternalCoroutinesApi
public abstract class ExecutorCoroutineDispatcherBase : ExecutorCoroutineDispatcher(), Delay {

    override fun dispatch(context: CoroutineContext, block: Runnable) =
        try { executor.execute(timeSource.trackTask(block)) }
        catch (e: RejectedExecutionException) {
            timeSource.unTrackTask()
            DefaultExecutor.execute(block)
        }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val timeout =
            try { (executor as? ScheduledExecutorService)
                ?.schedule(ResumeUndispatchedRunnable(this, continuation), timeMillis, TimeUnit.MILLISECONDS) }
            catch (e: RejectedExecutionException) { null }
        if (timeout != null)
            continuation.cancelFutureOnCancellation(timeout)
        else
            DefaultExecutor.scheduleResumeAfterDelay(timeMillis, continuation)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        val timeout =
            try { (executor as? ScheduledExecutorService)
                ?.schedule(block, timeMillis, TimeUnit.MILLISECONDS) }
            catch (e: RejectedExecutionException) { null }
        return if (timeout != null)
            DisposableFutureHandle(timeout)
        else
            DefaultExecutor.invokeOnTimeout(timeMillis, block)
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
