/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.rx2

import io.reactivex.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.internal.*

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
 * Coroutine context can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * Method throws [IllegalArgumentException] if provided [context] contains a [Job] instance.
 */
public fun rxCompletable(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> Unit
): Completable {
    require(context[Job] === null) { "Completable context cannot contain job in it." +
            "Its lifecycle should be managed via Disposable handle. Had $context" }
    return rxCompletableInternal(GlobalScope, context, block)
}

@Deprecated(
    message = "CoroutineScope.rxCompletable is deprecated in favour of top-level rxCompletable",
    level = DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("rxCompletable(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0
@LowPriorityInOverloadResolution
public fun CoroutineScope.rxCompletable(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> Unit
): Completable = rxCompletableInternal(this, context, block)

private fun rxCompletableInternal(
    scope: CoroutineScope, // support for legacy rxCompletable in scope
    context: CoroutineContext,
    block: suspend CoroutineScope.() -> Unit
): Completable = Completable.create { subscriber ->
    val newContext = scope.newCoroutineContext(context)
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
