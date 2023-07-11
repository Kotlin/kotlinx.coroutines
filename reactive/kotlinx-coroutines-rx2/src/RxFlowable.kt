/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.rx2

import io.reactivex.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.reactive.*
import kotlin.coroutines.*
import kotlin.internal.*

/**
 * Creates cold [flowable][Flowable] that will run a given [block] in a coroutine.
 * Every time the returned flowable is subscribed, it starts a new coroutine.
 *
 * Coroutine emits ([ObservableEmitter.onNext]) values with `send`, completes ([ObservableEmitter.onComplete])
 * when the coroutine completes or channel is explicitly closed and emits error ([ObservableEmitter.onError])
 * if coroutine throws an exception or closes channel with a cause.
 * Unsubscribing cancels running coroutine.
 *
 * Invocations of `send` are suspended appropriately when subscribers apply back-pressure and to ensure that
 * `onNext` is not invoked concurrently.
 *
 * Coroutine context can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * Method throws [IllegalArgumentException] if provided [context] contains a [Job] instance.
 *
 * **Note: This is an experimental api.** Behaviour of publishers that work as children in a parent scope with respect
 */
public fun <T: Any> rxFlowable(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Flowable<T> {
    require(context[Job] === null) { "Flowable context cannot contain job in it." +
            "Its lifecycle should be managed via Disposable handle. Had $context" }
    return Flowable.fromPublisher(publishInternal(GlobalScope, context, RX_HANDLER, block))
}

/** @suppress */
@Deprecated(
    message = "CoroutineScope.rxFlowable is deprecated in favour of top-level rxFlowable",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("rxFlowable(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0
@LowPriorityInOverloadResolution
public fun <T: Any> CoroutineScope.rxFlowable(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Flowable<T> = Flowable.fromPublisher(publishInternal(this, context, RX_HANDLER, block))

private val RX_HANDLER: (Throwable, CoroutineContext) -> Unit = ::handleUndeliverableException
