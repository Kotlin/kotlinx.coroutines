/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * Creates cold [Completable] that runs a given [block] in a coroutine.
 * Every time the returned completable is subscribed, it starts a new coroutine.
 * Unsubscribing cancels running coroutine.
 *
 * | **Coroutine action**                  | **Signal to subscriber**
 * | ------------------------------------- | ------------------------
 * | Completes successfully                | `onCompleted`
 * | Failure with exception or unsubscribe | `onError`
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * @param context context of the coroutine.
 * @param block the coroutine code.
 */
public fun CoroutineScope.rxCompletable(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> Unit
): Completable = Completable.create { subscriber ->
    val newContext = newCoroutineContext(context)
    val coroutine = RxCompletableCoroutine(newContext, subscriber)
    subscriber.setCancellable(RxCancellable(coroutine))
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

private class RxCompletableCoroutine(
    parentContext: CoroutineContext,
    private val subscriber: CompletableEmitter
) : AbstractCoroutine<Unit>(parentContext, true) {
    override fun onCompleted(value: Unit) {
        if (!subscriber.isDisposed) subscriber.onComplete()
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        if (!subscriber.isDisposed) {
            subscriber.onError(cause)
        } else if (!handled) {
            handleCoroutineException(context, cause)
        }
    }
}
