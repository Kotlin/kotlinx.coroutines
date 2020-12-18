/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.future

import kotlinx.coroutines.*
import kotlinx.coroutines.CancellationException
import java.util.concurrent.*
import java.util.function.*
import kotlin.coroutines.*

/**
 * Starts a new coroutine and returns its result as an implementation of [CompletableFuture].
 * The running coroutine is cancelled when the resulting future is cancelled or otherwise completed.
 *
 * The coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with the [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [context] element.
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
 * @param block the coroutine code.
 */
public fun <T> CoroutineScope.future(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
) : CompletableFuture<T> {
    require(!start.isLazy) { "$start start is not supported" }
    val newContext = this.newCoroutineContext(context)
    val future = CompletableFuture<T>()
    val coroutine = CompletableFutureCoroutine(newContext, future)
    future.whenComplete(coroutine) // Cancel coroutine if future was completed externally
    coroutine.start(start, coroutine, block)
    return future
}

private class CompletableFutureCoroutine<T>(
    context: CoroutineContext,
    private val future: CompletableFuture<T>
) : AbstractCoroutine<T>(context), BiConsumer<T?, Throwable?> {
    override fun accept(value: T?, exception: Throwable?) {
        cancel()
    }

    override fun onCompleted(value: T) {
        future.complete(value)
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        if (!future.completeExceptionally(cause) && !handled) {
            // prevents loss of exception that was not handled by parent & could not be set to CompletableFuture
            handleCoroutineException(context, cause)
        }
    }
}

/**
 * Converts this deferred value to the instance of [CompletableFuture].
 * The deferred value is cancelled when the resulting future is cancelled or otherwise completed.
 */
public fun <T> Deferred<T>.asCompletableFuture(): CompletableFuture<T> {
    val future = CompletableFuture<T>()
    setupCancellation(future)
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
 * Converts this job to the instance of [CompletableFuture].
 * The job is cancelled when the resulting future is cancelled or otherwise completed.
 */
public fun Job.asCompletableFuture(): CompletableFuture<Unit> {
    val future = CompletableFuture<Unit>()
    setupCancellation(future)
    invokeOnCompletion { cause ->
        if (cause === null) future.complete(Unit)
        else future.completeExceptionally(cause)
    }
    return future
}

private fun Job.setupCancellation(future: CompletableFuture<*>) {
    future.whenComplete { _, exception ->
        cancel(exception?.let {
            it as? CancellationException ?: CancellationException("CompletableFuture was completed exceptionally", it)
        })
    }
}

/**
 * Converts this [CompletionStage] to an instance of [Deferred].
 * When this completion stage is an instance of [Future], then it is cancelled when
 * the resulting deferred is cancelled.
 *
 * ### Implementation details
 *
 * [CompletionStage] does not extend a [Future] and does not provide future-like methods to check for completion and
 * to retrieve a resulting value, so this implementation always takes a slow path of installing a callback with
 * [CompletionStage.whenComplete]. For cases when [CompletionStage] is statically known to be an instance
 * of [CompletableFuture] there is an overload of this `asDeferred` function with a [CompletableFuture] receiver that
 * has a fast-path for a future that is already complete. Note, that it is not safe to dynamically check if an instance
 * of a [CompletionStage] is an instance of a [CompletableFuture], because JDK functions return instances that do
 * implement a [CompletableFuture], yet throw an [UnsupportedOperationException] on most of the future-like methods in it.
 * For the purpose of cancelling the the future, the corresponding [UnsupportedOperationException] is ignored in this case.
 */
@Suppress("DeferredIsResult")
public fun <T> CompletionStage<T>.asDeferred(): Deferred<T> {
    val result = CompletableDeferred<T>()
    whenComplete { value, exception ->
        if (exception == null) {
            // the future has completed normally
            result.complete(value)
        } else {
            // the future has completed with an exception, unwrap it consistently with fast path
            // Note: In the fast-path the implementation of CompletableFuture.get() does unwrapping
            result.completeExceptionally((exception as? CompletionException)?.cause ?: exception)
        }
    }
    if (this is Future<*>) result.cancelFutureOnCompletion(this)
    return result
}

/**
 * Converts this [CompletableFuture] to an instance of [Deferred].
 * The future is cancelled when the resulting deferred is cancelled.
 *
 * ### Implementation details
 *
 * This implementation has a fast-path for a case of a future that [isDone][CompletableFuture.isDone].
 */
@Suppress("DeferredIsResult")
public fun <T> CompletableFuture<T>.asDeferred(): Deferred<T> {
    // Fast path if already completed
    if (isDone) {
        return try {
            @Suppress("UNCHECKED_CAST")
            CompletableDeferred(get() as T)
        } catch (e: Throwable) {
            // unwrap original cause from ExecutionException
            val original = (e as? ExecutionException)?.cause ?: e
            CompletableDeferred<T>().also { it.completeExceptionally(original) }
        }
    }
    // slow-path
    return (this as CompletionStage<T>).asDeferred()
}
/**
 * Awaits for completion of [CompletionStage] without blocking a thread.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * stops waiting for the completion stage and immediately resumes with [CancellationException][kotlinx.coroutines.CancellationException].
 * This method is intended to be used with one-shot futures, so on coroutine cancellation completion stage is cancelled as well if it is instance of a [Future].
 * If cancelling given stage is undesired, `stage.asDeferred().await()` should be used instead.
 *
 * ### Implementation details
 *
 * [CompletionStage] does not extend a [Future] and does not provide future-like methods to check for completion and
 * to retrieve a resulting value, so this implementation always takes a slow path of installing a callback with
 * [CompletionStage.whenComplete]. For cases when [CompletionStage] is statically known to be an instance
 * of [CompletableFuture] there is an overload of this `await` function with a [CompletableFuture] receiver that
 * has a fast-path for a future that is already complete. Note, that it is not safe to dynamically check if an instance
 * of a [CompletionStage] is an instance of a [CompletableFuture], because JDK functions return instances that do
 * implement a [CompletableFuture], yet throw an exception on most of the future-like methods in it.
 * For the purpose of cancelling the the future, the corresponding [UnsupportedOperationException] is ignored in this case.
 */
public suspend fun <T> CompletionStage<T>.await(): T =
    suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
        val consumer = ContinuationConsumer(cont)
        whenComplete(consumer)
        if (cont.isActive) {
            // avoid creation of a lambda when continuation was already resumed during whenComplete call
            // TODO: In a major release this lambda can be made to extend CancelFutureOnCompletion class from core module
            // This will further save one allocated object here.
            cont.invokeOnCancellation {
                if (this is Future<*>) {
                    // mayInterruptIfRunning is not used
                    try {
                        cancel(false)
                    } catch (e: UnsupportedOperationException) {
                        // Internal JDK implementation of a Future can throw an UnsupportedOperationException here.
                        // We simply ignore it for the purpose of cancellation
                        // See https://github.com/Kotlin/kotlinx.coroutines/issues/2456
                    }
                }
                consumer.cont = null // shall clear reference to continuation to aid GC
            }
        }
    }

/**
 * Awaits for completion of [CompletableFuture] without blocking a thread.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * stops waiting for the completable future and immediately resumes with [CancellationException][kotlinx.coroutines.CancellationException].
 * This method is intended to be used with one-shot futures, so on coroutine cancellation the completable future is cancelled.
 * If cancelling the future is undesired, `future.asDeferred().await()` should be used instead.
 *
 * ### Implementation details
 *
 * This implementation has a fast-path for a case of a future that [isDone][CompletableFuture.isDone].
 */
public suspend fun <T> CompletableFuture<T>.await(): T {
    // fast path when CompletableFuture is already done (does not suspend)
    if (isDone) {
        try {
            @Suppress("UNCHECKED_CAST", "BlockingMethodInNonBlockingContext")
            return get() as T
        } catch (e: ExecutionException) {
            throw e.cause ?: e // unwrap original cause from ExecutionException
        }
    }
    // slow path -- suspend
    return (this as CompletionStage<T>).await()
}

private class ContinuationConsumer<T>(
    @Volatile @JvmField var cont: Continuation<T>?
) : BiConsumer<T?, Throwable?> {
    @Suppress("UNCHECKED_CAST")
    override fun accept(result: T?, exception: Throwable?) {
        val cont = this.cont ?: return // atomically read current value unless null
        if (exception == null) {
            // the future has completed normally
            cont.resume(result as T)
        } else {
            // the future has completed with an exception, unwrap it to provide consistent view of .await() result and to propagate only original exception
            cont.resumeWithException((exception as? CompletionException)?.cause ?: exception)
        }
    }
}
