/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.reactive.*
import kotlin.coroutines.experimental.*

/**
 * Creates cold [flowable][Flowable] that will run a given [block] in a coroutine.
 * Every time the returned flowable is subscribed, it starts a new coroutine.
 * Coroutine emits items with `send`. Unsubscribing cancels running coroutine.
 *
 * Invocations of `send` are suspended appropriately when subscribers apply back-pressure and to ensure that
 * `onNext` is not invoked concurrently.
 *
 * | **Coroutine action**                         | **Signal to subscriber**
 * | -------------------------------------------- | ------------------------
 * | `send`                                       | `onNext`
 * | Normal completion or `close` without cause   | `onComplete`
 * | Failure with exception or `close` with cause | `onError`
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * **Note: This is an experimental api.** Behaviour of publishers that work as children in a parent scope with respect
 *        to cancellation and error handling may change in the future.
 *        
 * @param context context of the coroutine.
 * @param block the coroutine code.
 */
@ExperimentalCoroutinesApi
public fun <T> CoroutineScope.rxFlowable(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend ProducerScope<T>.() -> Unit
): Flowable<T> = Flowable.fromPublisher(publish(newCoroutineContext(context), block = block))

/**
 * Creates cold [flowable][Flowable] that will run a given [block] in a coroutine.
 * @suppress **Deprecated** Use [CoroutineScope.rxFlowable] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.rxFlowable(context, block)",
        imports = ["kotlinx.coroutines.experimental.GlobalScope", "kotlinx.coroutines.experimental.rx2.rxFlowable"])
)
@JvmOverloads // for binary compatibility with older code compiled before context had a default
public fun <T> rxFlowable(
    context: CoroutineContext = Dispatchers.Default,
    block: suspend ProducerScope<T>.() -> Unit
): Flowable<T> = GlobalScope.rxFlowable(context, block)
