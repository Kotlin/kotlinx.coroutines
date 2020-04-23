/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import io.reactivex.rxjava3.core.*
import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * Creates cold [Completable] that runs a given [block] in a coroutine and emits its result.
 * Every time the returned completable is subscribed, it starts a new coroutine.
 * Unsubscribing cancels running coroutine.
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
        try {
            subscriber.onComplete()
        } catch (e: Throwable) {
            handleUndeliverableException(e, context)
        }
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        try {
            if (!subscriber.tryOnError(cause)) {
                handleUndeliverableException(cause, context)
            }
        } catch (e: Throwable) {
            handleUndeliverableException(e, context)
        }
    }
}
