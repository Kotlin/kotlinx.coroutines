/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:UseExperimental(ExperimentalTypeInference::class)

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.functions.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.experimental.*

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
@BuilderInference
public fun CoroutineScope.rxCompletable(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> Unit
): Completable = Completable.create { subscriber ->
    val newContext = newCoroutineContext(context)
    val coroutine = RxCompletableCoroutine(newContext, subscriber)
    subscriber.setCancellable(RxCancellable(coroutine))
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

/**
 * Creates cold [Completable] that runs a given [block] in a coroutine.
 * @suppress **Deprecated** Use [CoroutineScope.rxCompletable] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.rxCompletable(context, block)",
        imports = ["kotlinx.coroutines.GlobalScope", "kotlinx.coroutines.rx2.rxCompletable"])
)
public fun rxCompletable(
    context: CoroutineContext = Dispatchers.Default,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> Unit
): Completable = GlobalScope.rxCompletable(context + (parent ?: EmptyCoroutineContext), block)

private class RxCompletableCoroutine(
    parentContext: CoroutineContext,
    private val subscriber: CompletableEmitter
) : AbstractCoroutine<Unit>(parentContext, true) {
    override val cancelsParent: Boolean get() = true
    override fun onCompleted(value: Unit) {
        if (!subscriber.isDisposed) subscriber.onComplete()
    }

    override fun onCompletedExceptionally(exception: Throwable) {
        if (!subscriber.isDisposed) subscriber.onError(exception)
    }
}
