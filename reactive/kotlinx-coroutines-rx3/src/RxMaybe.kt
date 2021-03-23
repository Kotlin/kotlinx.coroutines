/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import io.reactivex.rxjava3.core.*
import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * Creates cold [maybe][Maybe] that will run a given [block] in a coroutine and emits its result.
 * If [block] result is `null`, [onComplete][MaybeObserver.onComplete] is invoked without a value.
 * Every time the returned observable is subscribed, it starts a new coroutine.
 * Unsubscribing cancels running coroutine.
 * Coroutine context can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * Method throws [IllegalArgumentException] if provided [context] contains a [Job] instance.
 */
public fun <T> rxMaybe(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Maybe<T> {
    require(context[Job] === null) { "Maybe context cannot contain job in it." +
            "Its lifecycle should be managed via Disposable handle. Had $context" }
    return rxMaybeInternal(GlobalScope, context, block)
}

private fun <T> rxMaybeInternal(
    scope: CoroutineScope, // support for legacy rxMaybe in scope
    context: CoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Maybe<T> = Maybe.create { subscriber ->
    val newContext = scope.newCoroutineContext(context)
    val coroutine = RxMaybeCoroutine(newContext, subscriber)
    subscriber.setCancellable(RxCancellable(coroutine))
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

private class RxMaybeCoroutine<T>(
    parentContext: CoroutineContext,
    private val subscriber: MaybeEmitter<T>
) : AbstractCoroutine<T>(parentContext, false, true) {
    override fun onCompleted(value: T) {
        try {
            if (value == null) subscriber.onComplete() else subscriber.onSuccess(value)
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
