/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*
import kotlin.js.*

/**
 * Starts new coroutine and returns its result as an implementation of [Promise].
 *
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [coroutineContext](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.coroutines.experimental/coroutine-context.html)
 * of the parent coroutine may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * The parent job may be also explicitly specified using [parent] parameter.
 *
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param parent explicitly specifies the parent job, overrides job from the [context] (if any).
 * @param onCompletion optional completion handler for the coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
public fun <T> promise(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): Promise<T> =
    GlobalScope.async(context + (parent ?: EmptyCoroutineContext), start, onCompletion, block = block).asPromise()

/**
 * Converts this deferred value to the instance of [Promise].
 */
public fun <T> Deferred<T>.asPromise(): Promise<T> {
    val promise = Promise<T> { resolve, reject ->
        invokeOnCompletion {
            val e = getCompletionExceptionOrNull()
            if (e != null) {
                reject(e)
            } else {
                resolve(getCompleted())
            }
        }
    }
    promise.asDynamic().deferred = this
    return promise
}

/**
 * Converts this promise value to the instance of [Deferred].
 */
public fun <T> Promise<T>.asDeferred(): Deferred<T> {
    val deferred = asDynamic().deferred
    @Suppress("UnsafeCastFromDynamic")
    return deferred ?: GlobalScope.async(start = CoroutineStart.UNDISPATCHED) { await() }
}

/**
 * Awaits for completion of the promise without blocking.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * stops waiting for the promise and immediately resumes with [CancellationException].
 */
public suspend fun <T> Promise<T>.await(): T = suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
    this@await.then(
        onFulfilled = { cont.resume(it) },
        onRejected = { cont.resumeWithException(it) })
}
