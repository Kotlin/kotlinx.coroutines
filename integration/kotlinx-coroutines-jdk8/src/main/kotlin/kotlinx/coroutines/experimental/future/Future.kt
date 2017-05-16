/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.future

import kotlinx.coroutines.experimental.*
import java.util.concurrent.CompletableFuture
import java.util.concurrent.CompletionStage
import java.util.function.BiConsumer
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.suspendCoroutine

/**
 * Starts new coroutine and returns its results an an implementation of [CompletableFuture].
 * This coroutine builder uses [CommonPool] context by default and is conceptually similar to [CompletableFuture.supplyAsync].
 *
 * The running coroutine is cancelled when the resulting future is cancelled or otherwise completed.
 * If the [context] for the new coroutine is explicitly specified and does not include a coroutine interceptor,
 * then [CoroutineDispatcher] element.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The specified context is added to the context of the parent running coroutine (if any) inside which this function
 * is invoked. The [Job] of the resulting coroutine is a child of the job of the parent coroutine (if any).
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * A value of [CoroutineStart.LAZY] is not supported
 * (since `ListenableFuture` framework does not provide the corresponding capability) and
 * produces [IllegalArgumentException].
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context context of the coroutine
 * @param start coroutine start option
 * @param block the coroutine code
 */
public fun <T> future(
    context: CoroutineContext = CommonPool,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): CompletableFuture<T> {
    require(!start.isLazy) { "$start start is not supported" }
    val newContext = newCoroutineContext(CommonPool + context)
    val job = Job(newContext[Job])
    val future = CompletableFutureCoroutine<T>(newContext + job)
    job.cancelFutureOnCompletion(future)
    future.whenComplete { _, exception -> job.cancel(exception) }
    start(block, receiver=future, completion=future)
    return future
}

private class CompletableFutureCoroutine<T>(
    override val context: CoroutineContext
) : CompletableFuture<T>(), Continuation<T>, CoroutineScope {
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
        } catch (exception: Exception) {
            future.completeExceptionally(exception)
        }
    }
    return future
}

/**
 * Awaits for completion of the completion stage without blocking a thread.
 *
 * This suspending function is not cancellable, because there is no way to cancel a `CompletionStage`.
 * Use `CompletableFuture.await()` for cancellation support.
 */
public suspend fun <T> CompletionStage<T>.await(): T = suspendCoroutine { cont: Continuation<T> ->
    whenComplete(ContinuationConsumer(cont))
}

/**
 * Awaits for completion of the future without blocking a thread.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
 * stops waiting for the future and immediately resumes with [CancellationException].
 */
public suspend fun <T> CompletableFuture<T>.await(): T {
    if (isDone) { // fast path when CompletableFuture is already done (does not suspend)
        // then only way to get unwrapped exception from the CompletableFuture is via whenComplete anyway
        var result: T? = null
        var exception: Throwable? = null
        whenComplete { r, e ->
            result = r
            exception = e
        }
        if (exception != null) throw exception!!
        return result as T
    }
    // slow path -- suspend
    return suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
        val consumer = ContinuationConsumer(cont)
        val completionFuture = whenComplete(consumer)
        cont.invokeOnCompletion {
            completionFuture.cancel(false) // cancel future
            consumer.cont = null // shall clear reference to continuation, because CompletableFuture continues to keep it
        }
    }
}

private class ContinuationConsumer<T>(
    @JvmField var cont: Continuation<T>?
) : BiConsumer<T?, Throwable?> {
    override fun accept(result: T?, exception: Throwable?) {
        val cont = this.cont ?: return // atomically read current value unless null, benign data race when it is set to null
        if (exception == null) // the future has been completed normally
            cont.resume(result as T)
        else // the future has completed with an exception
            cont.resumeWithException(exception)
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

@Deprecated("Use the other version. This one is for binary compatibility only.", level=DeprecationLevel.HIDDEN)
public fun <T> future(
    context: CoroutineContext = CommonPool,
    block: suspend () -> T
): CompletableFuture<T> = future(context=context) { block() }
