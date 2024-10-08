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
    future.handle(coroutine) // Cancel coroutine if future was completed externally
    coroutine.start(start, coroutine, block)
    return future
}

private class CompletableFutureCoroutine<T>(
    context: CoroutineContext,
    private val future: CompletableFuture<T>
) : AbstractCoroutine<T>(context, initParentJob = true, active = true), BiFunction<T?, Throwable?, Unit> {
    override fun apply(value: T?, exception: Throwable?) {
        cancel()
    }

    override fun onCompleted(value: T) {
        future.complete(value)
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        /*
         * Here we can potentially lose the cause if the failure is racing with future's
         * external cancellation. We are consistent with other future implementations
         * (LF, FT, CF) and give up on such exception.
         */
        future.completeExceptionally(cause)
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
    future.handle { _, exception ->
        cancel(exception?.let {
            it as? CancellationException ?: CancellationException("CompletableFuture was completed exceptionally", it)
        })
    }
}

/**
 * Converts this [CompletionStage] to an instance of [Deferred].
 *
 * The [CompletableFuture] that corresponds to this [CompletionStage] (see [CompletionStage.toCompletableFuture])
 * is cancelled when the resulting deferred is cancelled.
 */
@Suppress("DeferredIsResult")
public fun <T> CompletionStage<T>.asDeferred(): Deferred<T> {
    val future = toCompletableFuture() // retrieve the future
    // Fast path if already completed
    if (future.isDone) {
        return try {
            @Suppress("UNCHECKED_CAST")
            CompletableDeferred(future.get() as T)
        } catch (e: Throwable) {
            // unwrap original cause from ExecutionException
            val original = (e as? ExecutionException)?.cause ?: e
            CompletableDeferred<T>().also { it.completeExceptionally(original) }
        }
    }
    val result = CompletableDeferred<T>()
    handle { value, exception ->
        try {
            if (exception == null) {
                // the future has completed normally
                result.complete(value)
            } else {
                // the future has completed with an exception, unwrap it consistently with fast path
                // Note: In the fast-path the implementation of CompletableFuture.get() does unwrapping
                result.completeExceptionally((exception as? CompletionException)?.cause ?: exception)
            }
        } catch (e: Throwable) {
            // We come here iff the internals of Deferred threw an exception during its completion
            handleCoroutineException(EmptyCoroutineContext, e)
        }
    }
    result.invokeOnCompletion(handler = CancelFutureOnCompletion(future))
    return result
}

/**
 * Awaits for completion of [CompletionStage] without blocking a thread.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled while this suspending function is waiting, this function
 * stops waiting for the completion stage and immediately resumes with [CancellationException][kotlinx.coroutines.CancellationException].
 *
 * This method is intended to be used with one-shot futures, so on coroutine cancellation the [CompletableFuture] that
 * corresponds to this [CompletionStage] (see [CompletionStage.toCompletableFuture])
 * is cancelled. If cancelling the given stage is undesired, `stage.asDeferred().await()` should be used instead.
 */
public suspend fun <T> CompletionStage<T>.await(): T {
    val future = toCompletableFuture() // retrieve the future
    // fast path when CompletableFuture is already done (does not suspend)
    if (future.isDone) {
        try {
            @Suppress("UNCHECKED_CAST", "BlockingMethodInNonBlockingContext")
            return future.get() as T
        } catch (e: ExecutionException) {
            throw e.cause ?: e // unwrap original cause from ExecutionException
        }
    }
    // slow path -- suspend
    return suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
        val consumer = ContinuationHandler(cont)
        handle(consumer)
        cont.invokeOnCancellation {
            future.cancel(false)
            consumer.cont = null // shall clear reference to continuation to aid GC
        }
    }
}

private class ContinuationHandler<T>(
    @Volatile @JvmField var cont: Continuation<T>?
) : BiFunction<T?, Throwable?, Unit> {
    @Suppress("UNCHECKED_CAST")
    override fun apply(result: T?, exception: Throwable?) {
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

private class CancelFutureOnCompletion(
    private val future: Future<*>
) : JobNode() {
    override val onCancelling get() = false

    override fun invoke(cause: Throwable?) {
        // Don't interrupt when cancelling future on completion, because no one is going to reset this
        // interruption flag and it will cause spurious failures elsewhere.
        // We do not cancel the future if it's already completed in some way,
        // because `cancel` on a completed future won't change the state but is not guaranteed to behave well
        // on reentrancy. See https://github.com/Kotlin/kotlinx.coroutines/issues/4156
        if (cause != null && !future.isDone) future.cancel(false)
    }
}
