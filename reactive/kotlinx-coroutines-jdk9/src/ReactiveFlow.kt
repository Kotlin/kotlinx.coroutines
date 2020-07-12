/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.jdk9

import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.asFlow
import kotlinx.coroutines.reactive.asPublisher
import kotlinx.coroutines.reactive.collect
import java.util.concurrent.Flow as JFlow
import org.reactivestreams.FlowAdapters

/**
 * Transforms the given reactive [Publisher] into [Flow].
 * Use [buffer] operator on the resulting flow to specify the size of the backpressure.
 * More precisely, it specifies the value of the subscription's [request][Subscription.request].
 * [buffer] default capacity is used by default.
 *
 * If any of the resulting flow transformations fails, subscription is immediately cancelled and all in-flight elements
 * are discarded.
 */
public fun <T : Any> JFlow.Publisher<T>.asFlow(): Flow<T> =
        FlowAdapters.toPublisher(this).asFlow()

/**
 * Transforms the given flow to a reactive specification compliant [Publisher].
 */
public fun <T : Any> Flow<T>.asPublisher(): JFlow.Publisher<T> {
    val reactivePublisher : org.reactivestreams.Publisher<T> = this.asPublisher<T>()
    return FlowAdapters.toFlowPublisher(reactivePublisher)
}

/**
 * Subscribes to this [Publisher] and performs the specified action for each received element.
 * Cancels subscription if any exception happens during collect.
 */
public suspend inline fun <T> JFlow.Publisher<T>.collect(action: (T) -> Unit): Unit =
    FlowAdapters.toPublisher(this).collect(action)
