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

package kotlinx.coroutines.experimental.guava

import com.google.common.util.concurrent.AbstractFuture
import com.google.common.util.concurrent.FutureCallback
import com.google.common.util.concurrent.Futures
import com.google.common.util.concurrent.ListenableFuture
import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Starts new coroutine and returns its results an an implementation of [ListenableFuture].
 * This coroutine builder uses [CommonPool] context by default.
 *
 * The running coroutine is cancelled when the resulting future is cancelled or otherwise completed.
 * If the [context] for the new coroutine is omitted or is explicitly specified but does not include a
 * coroutine interceptor, then [CommonPool] is used.
 * See [CoroutineDispatcher] for other standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
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
): ListenableFuture<T> {
    require(!start.isLazy) { "$start start is not supported" }
    val newContext = newCoroutineContext(CommonPool + context)
    val job = Job(newContext[Job])
    val future = ListenableFutureCoroutine<T>(newContext + job)
    job.cancelFutureOnCompletion(future)
    start(block, receiver=future, completion=future) // use the specified start strategy
    return future
}

private class ListenableFutureCoroutine<T>(
    override val context: CoroutineContext
) : AbstractFuture<T>(), Continuation<T>, CoroutineScope {
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
public suspend fun <T> ListenableFuture<T>.await(): T = suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
    val callback = ContinuationCallback(cont)
    Futures.addCallback(this, callback)
    cont.invokeOnCompletion {
        callback.cont = null // clear the reference to continuation from the future's callback
    }
}

private class ContinuationCallback<T>(
    @Volatile @JvmField var cont: Continuation<T>?
) : FutureCallback<T> {
    @Suppress("UNCHECKED_CAST")
    override fun onSuccess(result: T?) { cont?.resume(result as T) }
    override fun onFailure(t: Throwable) { cont?.resumeWithException(t) }
}
