/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*
import kotlin.js.*

/**
 * Starts new coroutine and returns its result as an implementation of [Promise].
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param onCompletion optional completion handler for the coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
public fun <T> CoroutineScope.promise(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): Promise<T> =
    async(context, start, onCompletion, block = block).asPromise()

/**
 * Starts new coroutine and returns its result as an implementation of [Promise].
 * @suppress **Deprecated**. Use [CoroutineScope.promise] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.promise(context + parent, start, onCompletion, block)",
        imports = ["kotlinx.coroutines.experimental.*"])
)
public fun <T> promise(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): Promise<T> =
    GlobalScope.promise(context, start, onCompletion, block = block)

/**
 * Starts new coroutine and returns its result as an implementation of [Promise].
 * @suppress **Deprecated**. Use [CoroutineScope.promise] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.promise(context + parent, start, onCompletion, block)",
        imports = ["kotlinx.coroutines.experimental.*"])
)
public fun <T> promise(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): Promise<T> =
    GlobalScope.promise(context + (parent ?: EmptyCoroutineContext), start, onCompletion, block = block)

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
