/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.flowOn
import kotlinx.coroutines.reactive.FlowSubscription
import org.reactivestreams.*
import reactor.core.CoreSubscriber
import reactor.core.publisher.Flux
import kotlin.coroutines.*

/**
 * Converts the given flow to a cold flux.
 * The original flow is cancelled when the flux subscriber is disposed.
 *
 * This function is integrated with [ReactorContext], see its documentation for additional details.
 *
 * An optional [context] can be specified to control the execution context of calls to [Subscriber] methods.
 * You can set a [CoroutineDispatcher] to confine them to a specific thread and/or various [ThreadContextElement] to
 * inject additional context into the caller thread. By default, the [Unconfined][Dispatchers.Unconfined] dispatcher
 * is used, so calls are performed from an arbitrary thread.
 */
@JvmOverloads // binary compatibility
public fun <T: Any> Flow<T>.asFlux(context: CoroutineContext = EmptyCoroutineContext): Flux<T> =
    FlowAsFlux(this, Dispatchers.Unconfined + context)

private class FlowAsFlux<T : Any>(
    private val flow: Flow<T>,
    private val context: CoroutineContext
) : Flux<T>() {
    override fun subscribe(subscriber: CoreSubscriber<in T>) {
        val hasContext = !subscriber.currentContext().isEmpty
        val source = if (hasContext) flow.flowOn(subscriber.currentContext().asCoroutineContext()) else flow
        subscriber.onSubscribe(FlowSubscription(source, subscriber, context))
    }
}
