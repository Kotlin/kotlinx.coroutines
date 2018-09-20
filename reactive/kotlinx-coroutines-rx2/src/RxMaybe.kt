/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import io.reactivex.functions.*
import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

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
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * @param context context of the coroutine.
 * @param block the coroutine code.
 */
public fun <T> CoroutineScope.rxMaybe(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T?
): Maybe<T> = Maybe.create { subscriber ->
    val newContext = newCoroutineContext(context)
    val coroutine = RxMaybeCoroutine(newContext, subscriber)
    subscriber.setCancellable(RxCancellable(coroutine))
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

/**
 * Creates cold [maybe][Maybe] that will run a given [block] in a coroutine.
 * @suppress **Deprecated** Use [CoroutineScope.rxMaybe] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.rxMaybe(context, block)",
        imports = ["kotlinx.coroutines.experimental.GlobalScope", "kotlinx.coroutines.experimental.rx2.rxMaybe"])
)
public fun <T> rxMaybe(
    context: CoroutineContext = Dispatchers.Default,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> T?
): Maybe<T> = GlobalScope.rxMaybe(context + (parent ?: EmptyCoroutineContext), block)

private class RxMaybeCoroutine<T>(
    parentContext: CoroutineContext,
    private val subscriber: MaybeEmitter<T>
) : AbstractCoroutine<T>(parentContext, true) {
    override fun onCompleted(value: T) {
        if (!subscriber.isDisposed) {
            if (value == null) subscriber.onComplete() else subscriber.onSuccess(value)
        }
    }

    override fun onCompletedExceptionally(exception: Throwable) {
        if (!subscriber.isDisposed) subscriber.onError(exception)
    }
}
