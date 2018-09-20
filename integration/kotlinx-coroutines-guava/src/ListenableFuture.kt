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
 * The running coroutine is cancelled when the resulting future is cancelled or otherwise completed.
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * A value of [CoroutineStart.LAZY] is not supported
 * (since `ListenableFuture` framework does not provide the corresponding capability) and
 * produces [IllegalArgumentException].
 *
 * See [newCoroutineContext][CoroutineScope.newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param block the coroutine code.
 */
public fun <T> CoroutineScope.future(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): ListenableFuture<T> {
    require(!start.isLazy) { "$start start is not supported" }
    val newContext = newCoroutineContext(context)
    val job = Job(newContext[Job])
    val future = ListenableFutureCoroutine<T>(newContext + job)
    job.cancelFutureOnCompletion(future)
    start(block, receiver=future, completion=future) // use the specified start strategy
    return future
}

/**
 * @suppress **Deprecated**: onCompletion parameter is deprecated.
 */
@Deprecated("onCompletion parameter is deprecated")
public fun <T> CoroutineScope.future(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): ListenableFuture<T> {
    require(!start.isLazy) { "$start start is not supported" }
    val newContext = newCoroutineContext(context)
    val job = Job(newContext[Job])
    val future = ListenableFutureCoroutine<T>(newContext + job)
    job.cancelFutureOnCompletion(future)
    if (onCompletion != null) job.invokeOnCompletion(handler = onCompletion)
    start(block, receiver=future, completion=future) // use the specified start strategy
    return future
}

/**
 * Starts new coroutine and returns its results an an implementation of [ListenableFuture].
 * @suppress **Deprecated**. Use [CoroutineScope.future] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.future(context, start, onCompletion, block)",
        imports = ["kotlinx.coroutines.experimental.GlobalScope", "kotlinx.coroutines.experimental.future.future"])
)
public fun <T> future(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): ListenableFuture<T> =
    GlobalScope.future(context, start, onCompletion, block)

/**
 * Starts new coroutine and returns its results an an implementation of [ListenableFuture].
 * @suppress **Deprecated**. Use [CoroutineScope.future] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.future(context + parent, start, onCompletion, block)",
        imports = ["kotlinx.coroutines.experimental.GlobalScope", "kotlinx.coroutines.experimental.future.future"])
)
public fun <T> future(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): ListenableFuture<T> =
    GlobalScope.future(context + (parent ?: EmptyCoroutineContext), start, onCompletion, block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <T> future(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> T
): ListenableFuture<T> =
    GlobalScope.future(context + (parent ?: EmptyCoroutineContext), start, block = block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <T> future(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): ListenableFuture<T> =
    GlobalScope.future(context, start, block = block)

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
            } catch (t: Throwable) {
                setException(t)
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
 * stops waiting for the future and immediately resumes with [CancellationException][kotlinx.coroutines.experimental.CancellationException].
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
