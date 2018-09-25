/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.future

import kotlinx.coroutines.experimental.*
import java.util.concurrent.*
import java.util.function.*
import kotlin.coroutines.experimental.*

/**
 * Starts new coroutine and returns its result as an implementation of [CompletableFuture].
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
 * (since `CompletableFuture` framework does not provide the corresponding capability) and
 * produces [IllegalArgumentException].
 *
 * See [newCoroutineContext][CoroutineScope.newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param onCompletion optional completion handler for the coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
public fun <T> CoroutineScope.future(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): CompletableFuture<T> {
    require(!start.isLazy) { "$start start is not supported" }
    val newContext = this.newCoroutineContext(context)
    val job = Job(newContext[Job])
    val future = CompletableFutureCoroutine<T>(newContext + job)
    job.cancelFutureOnCompletion(future)
    future.whenComplete { _, exception -> job.cancel(exception) }
    if (onCompletion != null) job.invokeOnCompletion(handler = onCompletion)
    start(block, receiver=future, completion=future) // use the specified start strategy
    return future
}

/**
 * Starts new coroutine and returns its result as an implementation of [CompletableFuture].
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
): CompletableFuture<T> =
    GlobalScope.future(context, start, onCompletion, block)

/**
 * Starts new coroutine and returns its result as an implementation of [CompletableFuture].
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
): CompletableFuture<T> =
    GlobalScope.future(context + (parent ?: EmptyCoroutineContext), start, onCompletion, block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <T> future(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> T
): CompletableFuture<T> =
    GlobalScope.future(context + (parent ?: EmptyCoroutineContext), start, block = block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <T> future(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): CompletableFuture<T> =
    GlobalScope.future(context, start, block = block)

private class CompletableFutureCoroutine<T>(
    override val context: CoroutineContext
) : CompletableFuture<T>(), Continuation<T>, CoroutineScope {
    override val coroutineContext: CoroutineContext get() = context
    override val isActive: Boolean get() = context[Job]!!.isActive
    override fun resume(value: T) { complete(value) }
    override fun resumeWithException(exception: Throwable) { completeExceptionally(exception) }
}

/**
 * Converts this deferred value to the instance of [CompletableFuture].
 * The deferred value is cancelled when the resulting future is cancelled or otherwise completed.
 */
public fun <T> Deferred<T>.asCompletableFuture(): CompletableFuture<T> {
    val future = CompletableFuture<T>()
    future.whenComplete { _, exception -> cancel(exception) }
    invokeOnCompletion {
        try {
            future.complete(getCompleted())
        } catch (t: Throwable) {
            future.completeExceptionally(t)
        }
    }
    return future
}

/**
 * Converts this completion stage to an instance of [Deferred].
 * When this completion stage is an instance of [Future], then it is cancelled when
 * the resulting deferred is cancelled.
 */
public fun <T> CompletionStage<T>.asDeferred(): Deferred<T> {
    // Fast path if already completed
    if (this is Future<*> && isDone()){
        return try {
            @Suppress("UNCHECKED_CAST")
            CompletableDeferred(get() as T)
        } catch (e: Throwable) {
            // unwrap original cause from ExecutionException
            val original = (e as? ExecutionException)?.cause ?: e
            CompletableDeferred<T>().also { it.cancel(original) }
        }
    }
    val result = CompletableDeferred<T>()
    whenComplete { value, exception ->
        if (exception == null) {
            result.complete(value)
        } else {
            result.cancel(exception)
        }
    }
    if (this is Future<*>) result.cancelFutureOnCompletion(this)
    return result
}

/**
 * Awaits for completion of the future without blocking a thread.
 *
 * @suppress **Deprecated**: For binary compatibility only
 */
@Deprecated("For binary compatibility only", level = DeprecationLevel.HIDDEN)
public suspend fun <T> CompletableFuture<T>.await(): T =
    (this as CompletionStage<T>).await()

/**
 * Awaits for completion of the completion stage without blocking a thread.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * stops waiting for the completion stage and immediately resumes with [CancellationException][kotlinx.coroutines.experimental.CancellationException].
 *
 * Note, that `CompletionStage` implementation does not support prompt removal of installed listeners, so on cancellation of this wait
 * a few small objects will remain in the `CompletionStage` stack of completion actions until it completes itself.
 * However, the care is taken to clear the reference to the waiting coroutine itself, so that its memory can be
 * released even if the completion stage never completes.
 */
public suspend fun <T> CompletionStage<T>.await(): T {
    // fast path when CompletableFuture is already done (does not suspend)
    if (this is Future<*> && isDone()) {
        try {
            @Suppress("UNCHECKED_CAST")
            return get() as T
        } catch (e: ExecutionException) {
            throw e.cause ?: e // unwrap original cause from ExecutionException
        }
    }
    // slow path -- suspend
    return suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
        val consumer = ContinuationConsumer(cont)
        whenComplete(consumer)
        cont.invokeOnCancellation {
            consumer.cont = null // shall clear reference to continuation
        }
    }
}

private class ContinuationConsumer<T>(
    @Volatile @JvmField var cont: Continuation<T>?
) : BiConsumer<T?, Throwable?> {
    @Suppress("UNCHECKED_CAST")
    override fun accept(result: T?, exception: Throwable?) {
        val cont = this.cont ?: return // atomically read current value unless null
        if (exception == null) {
            // the future has been completed normally
            cont.resume(result as T)
        } else {
            // the future has completed with an exception, unwrap it to provide consistent view of .await() result and to propagate only original exception
            cont.resumeWithException((exception as? CompletionException)?.cause ?: exception)
        }
    }
}

// --------------------------------------- DEPRECATED APIs ---------------------------------------
// We keep it only for backwards compatibility with old versions of this integration library.
// Do not copy when using this file an example for other integration.

/**
 * Converts this deferred value to the instance of [CompletableFuture].
 * The deferred value is cancelled when the resulting future is cancelled or otherwise completed.
 * @suppress: **Deprecated**: Renamed to [asCompletableFuture]
 */
@Deprecated("Renamed to `asCompletableFuture`",
    replaceWith = ReplaceWith("asCompletableFuture()"))
public fun <T> Deferred<T>.toCompletableFuture(): CompletableFuture<T> = asCompletableFuture()

/** @suppress **Deprecated** */
@Suppress("DeprecatedCallableAddReplaceWith") // todo: the warning is incorrectly shown, see KT-17917
@Deprecated("Use the other version. This one is for binary compatibility only.", level=DeprecationLevel.HIDDEN)
public fun <T> future(
    context: CoroutineContext = Dispatchers.Default,
    block: suspend () -> T
): CompletableFuture<T> =
    GlobalScope.future(context = context, block = { block() })
