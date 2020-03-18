/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.flowOn
import kotlinx.coroutines.reactive.FlowSubscription
import reactor.core.CoreSubscriber
import reactor.core.publisher.Flux

/**
 * Converts the given flow to a cold flux.
 * The original flow is cancelled when the flux subscriber is disposed.
 *
 * This function is integrated with [ReactorContext], see its documentation for additional details.
 */
public fun <T: Any> Flow<T>.asFlux(): Flux<T> = FlowAsFlux(this)

private class FlowAsFlux<T : Any>(private val flow: Flow<T>) : Flux<T>() {
    override fun subscribe(subscriber: CoreSubscriber<in T>?) {
        if (subscriber == null) throw NullPointerException()
        val hasContext = !subscriber.currentContext().isEmpty
        val source = if (hasContext) flow.flowOn(subscriber.currentContext().asCoroutineContext()) else flow
        subscriber.onSubscribe(FlowSubscription(source, subscriber))
    }
}
