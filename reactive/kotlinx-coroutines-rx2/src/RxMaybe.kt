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
 * Creates cold [maybe][Maybe] that will run a given [block] in a coroutine.
 * Every time the returned observable is subscribed, it starts a new coroutine.
 * Coroutine returns a single, possibly null value. Unsubscribing cancels running coroutine.
 *
 * | **Coroutine action**                  | **Signal to subscriber**
 * | ------------------------------------- | ------------------------
 * | Returns a non-null value              | `onSuccess`
 * | Returns a null                        | `onComplete`
 * | Failure with exception or unsubscribe | `onError`
 *
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

@Deprecated(
    message = "CoroutineScope.rxMaybe is deprecated in favour of top-level rxMaybe",
    level = DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("rxMaybe(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0
@LowPriorityInOverloadResolution
public fun <T> CoroutineScope.rxMaybe(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Maybe<T> = rxMaybeInternal(this, context, block)

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
) : AbstractCoroutine<T>(parentContext, true) {
    override fun onCompleted(value: T) {
        if (!subscriber.isDisposed) {
            if (value == null) subscriber.onComplete() else subscriber.onSuccess(value)
        }
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        if (!subscriber.isDisposed) {
            subscriber.onError(cause)
        } else if (!handled) {
            handleCoroutineException(context, cause)
        }
    }
}
