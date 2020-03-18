/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.rx2

import io.reactivex.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.internal.*

/**
 * Creates cold [single][Single] that will run a given [block] in a coroutine and emits its result.
 * Every time the returned observable is subscribed, it starts a new coroutine.
 * Unsubscribing cancels running coroutine.
 * Coroutine context can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * Method throws [IllegalArgumentException] if provided [context] contains a [Job] instance.
 */
public fun <T : Any> rxSingle(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T
): Single<T> {
    require(context[Job] === null) { "Single context cannot contain job in it." +
            "Its lifecycle should be managed via Disposable handle. Had $context" }
    return rxSingleInternal(GlobalScope, context, block)
}

@Deprecated(
    message = "CoroutineScope.rxSingle is deprecated in favour of top-level rxSingle",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("rxSingle(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0
@LowPriorityInOverloadResolution
public fun <T : Any> CoroutineScope.rxSingle(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T
): Single<T> = rxSingleInternal(this, context, block)

private fun <T : Any> rxSingleInternal(
    scope: CoroutineScope, // support for legacy rxSingle in scope
    context: CoroutineContext,
    block: suspend CoroutineScope.() -> T
): Single<T> = Single.create { subscriber ->
    val newContext = scope.newCoroutineContext(context)
    val coroutine = RxSingleCoroutine(newContext, subscriber)
    subscriber.setCancellable(RxCancellable(coroutine))
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

private class RxSingleCoroutine<T: Any>(
    parentContext: CoroutineContext,
    private val subscriber: SingleEmitter<T>
) : AbstractCoroutine<T>(parentContext, true) {
    override fun onCompleted(value: T) {
        try {
            subscriber.onSuccess(value)
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
