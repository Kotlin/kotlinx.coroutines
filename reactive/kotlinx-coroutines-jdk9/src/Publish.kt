/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.jdk9

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import java.util.concurrent.*
import kotlin.coroutines.*
import org.reactivestreams.FlowAdapters

/**
 * Creates cold reactive [Flow.Publisher] that runs a given [block] in a coroutine.
 * Every time the returned flux is subscribed, it starts a new coroutine in the specified [context].
 * Coroutine emits ([Subscriber.onNext]) values with `send`, completes ([Subscriber.onComplete])
 * when the coroutine completes or channel is explicitly closed and emits error ([Subscriber.onError])
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
 *        to cancellation and error handling may change in the future.
 */
@ExperimentalCoroutinesApi
public fun <T> flowPublish(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Flow.Publisher<T> {
    val reactivePublisher : org.reactivestreams.Publisher<T> = kotlinx.coroutines.reactive.publish<T>(context, block)
    return FlowAdapters.toFlowPublisher(reactivePublisher)
}
