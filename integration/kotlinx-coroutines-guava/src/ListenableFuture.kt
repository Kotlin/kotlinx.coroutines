/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.guava

import com.google.common.util.concurrent.*
import kotlinx.coroutines.experimental.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

/**
 * Starts new coroutine and returns its results an an implementation of [ListenableFuture].
 * This coroutine builder uses [CommonPool] context by default.
 *
 * The running coroutine is cancelled when the resulting future is cancelled or otherwise completed.
 *
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [coroutineContext] of the parent coroutine may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * The parent job may be also explicitly specified using [parent] parameter.
 *
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * A value of [CoroutineStart.LAZY] is not supported
 * (since `ListenableFuture` framework does not provide the corresponding capability) and
 * produces [IllegalArgumentException].
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param parent explicitly specifies the parent job, overrides job from the [context] (if any).
 * @param onCompletion optional completion handler for the coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
public fun <T> future(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): ListenableFuture<T> {
    require(!start.isLazy) { "$start start is not supported" }
    val newContext = newCoroutineContext(context, parent)
    val job = Job(newContext[Job])
    val future = ListenableFutureCoroutine<T>(newContext + job)
    job.cancelFutureOnCompletion(future)
    if (onCompletion != null) job.invokeOnCompletion(handler = onCompletion)
    start(block, receiver=future, completion=future) // use the specified start strategy
    return future
}

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <T> future(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> T
): ListenableFuture<T> = future(context, start, parent, block = block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <T> future(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): ListenableFuture<T> =
    future(context, start, block = block)

private class ListenableFutureCoroutine<T>(
    override val context: CoroutineContext
) : AbstractFuture<T>(), Continuation<T>, CoroutineScope {
    override val coroutineContext: CoroutineContext get() = context
    override val isActive: Boolean get() = context[Job]!!.isActive
    override fun resume(value: T) { set(value) }
    override fun resumeWithException(exception: Throwable) { setException(exception) }
    override fun interruptTask() { context[Job]!!.cancel() }
}

/**
 * Converts this deferred value to the instance of [ListenableFuture].
 * The deferred value is cancelled when the resulting future is cancelled or otherwise completed.
 */
public fun <T> Deferred<T>.asListenableFuture(): ListenableFuture<T> = DeferredListenableFuture<T>(this)

private class DeferredListenableFuture<T>(
    private val deferred: Deferred<T>
) : AbstractFuture<T>() {
    init {
        deferred.invokeOnCompletion {
            try {
                set(deferred.getCompleted())
            } catch (exception: Exception) {
                setException(exception)
            }
        }
    }
    override fun interruptTask() { deferred.cancel() }
}

/**
 * Awaits for completion of the future without blocking a thread.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * stops waiting for the future and immediately resumes with [CancellationException].
 *
 * Note, that `ListenableFuture` does not support removal of installed listeners, so on cancellation of this wait
 * a few small objects will remain in the `ListenableFuture` list of listeners until the future completes. However, the
 * care is taken to clear the reference to the waiting coroutine itself, so that its memory can be released even if
 * the future never completes.
 */
public suspend fun <T> ListenableFuture<T>.await(): T {
    try {
        if (isDone) return get() as T
    } catch (e: ExecutionException) {
        throw e.cause ?: e // unwrap original cause from ExecutionException
    }

    return suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
        val callback = ContinuationCallback(cont)
        Futures.addCallback(this, callback, MoreExecutors.directExecutor())
        cont.invokeOnCancellation {
            callback.cont = null // clear the reference to continuation from the future's callback
        }
    }
}

private class ContinuationCallback<T>(
    @Volatile @JvmField var cont: Continuation<T>?
) : FutureCallback<T> {
    @Suppress("UNCHECKED_CAST")
    override fun onSuccess(result: T?) { cont?.resume(result as T) }
    override fun onFailure(t: Throwable) { cont?.resumeWithException(t) }
}
