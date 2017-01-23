package kotlinx.coroutines.experimental.future

import kotlinx.coroutines.experimental.*
import java.util.concurrent.CompletableFuture
import kotlin.coroutines.Continuation
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.startCoroutine

/**
 * Starts new coroutine and returns its results an an implementation of [CompletableFuture].
 * This coroutine builder uses [CommonPool] context by default and is conceptually similar to [CompletableFuture.supplyAsync].
 *
 * The running coroutine is cancelled when the resulting future is cancelled or otherwise completed.
 * If the [context] for the new coroutine is explicitly specified, then it must include [CoroutineDispatcher] element.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The specified context is added to the context of the parent running coroutine (if any) inside which this function
 * is invoked. The [Job] of the resulting coroutine is a child of the job of the parent coroutine (if any).
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 */
public fun <T> future(context: CoroutineContext = CommonPool, block: suspend () -> T): CompletableFuture<T> {
    val newContext = newCoroutineContext(CommonPool + context)
    val job = Job(newContext[Job])
    val future = CompletableFutureCoroutine<T>(newContext + job)
    job.cancelFutureOnCompletion(future)
    future.whenComplete { _, exception -> job.cancel(exception) }
    block.startCoroutine(future)
    return future
}

/**
 * Converts this deferred value to the instance of [CompletableFuture].
 * The deferred value is cancelled when the resulting future is cancelled or otherwise completed.
 */
public fun <T> Deferred<T>.toCompletableFuture(): CompletableFuture<T> {
    val future = CompletableFuture<T>()
    future.whenComplete { _, exception -> cancel(exception) }
    onCompletion {
        try {
            future.complete(getCompleted())
        } catch (exception: Exception) {
            future.completeExceptionally(exception)
        }
    }
    return future
}

/**
 * Awaits for completion of the future without blocking a thread. This suspending function is cancellable.
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException] .
 */
public suspend fun <T> CompletableFuture<T>.await(): T {
    if (isDone) {
        // then only way to get unwrapped exception from the CompletableFuture...
        var result: T? = null
        var exception: Throwable? = null
        whenComplete { r, e ->
            result = r
            exception = e
        }
        if (exception != null) throw exception!!
        return result as T
    }
    return suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
        val completionFuture = whenComplete { result, exception ->
            if (exception == null) // the future has been completed normally
                cont.resume(result)
            else // the future has completed with an exception
                cont.resumeWithException(exception)
        }
        cont.cancelFutureOnCompletion(completionFuture)
        Unit
    }
}

private class CompletableFutureCoroutine<T>(
    override val context: CoroutineContext
) : CompletableFuture<T>(), Continuation<T> {
    override fun resume(value: T) { complete(value) }
    override fun resumeWithException(exception: Throwable) { completeExceptionally(exception) }
}
