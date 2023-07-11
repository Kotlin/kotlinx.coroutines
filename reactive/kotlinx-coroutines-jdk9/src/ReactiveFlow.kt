/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.jdk9

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.asFlow
import kotlinx.coroutines.reactive.asPublisher as asReactivePublisher
import kotlinx.coroutines.reactive.collect
import kotlinx.coroutines.channels.*
import org.reactivestreams.*
import kotlin.coroutines.*
import java.util.concurrent.Flow as JFlow

/**
 * Transforms the given reactive [Flow Publisher][JFlow.Publisher] into [Flow].
 * Use the [buffer] operator on the resulting flow to specify the size of the back-pressure.
 * In effect, it specifies the value of the subscription's [request][JFlow.Subscription.request].
 * The [default buffer capacity][Channel.BUFFERED] for a suspending channel is used by default.
 *
 * If any of the resulting flow transformations fails, the subscription is immediately cancelled and all the in-flight
 * elements are discarded.
 */
public fun <T : Any> JFlow.Publisher<T>.asFlow(): Flow<T> =
    FlowAdapters.toPublisher(this).asFlow()

/**
 * Transforms the given flow into a reactive specification compliant [Flow Publisher][JFlow.Publisher].
 *
 * An optional [context] can be specified to control the execution context of calls to the [Flow Subscriber][Subscriber]
 * methods.
 * A [CoroutineDispatcher] can be set to confine them to a specific thread; various [ThreadContextElement] can be set to
 * inject additional context into the caller thread. By default, the [Unconfined][Dispatchers.Unconfined] dispatcher
 * is used, so calls are performed from an arbitrary thread.
 */
@JvmOverloads // binary compatibility
public fun <T : Any> Flow<T>.asPublisher(context: CoroutineContext = EmptyCoroutineContext): JFlow.Publisher<T> =
    FlowAdapters.toFlowPublisher(asReactivePublisher(context))

/**
 * Subscribes to this [Flow Publisher][JFlow.Publisher] and performs the specified action for each received element.
 *
 * If [action] throws an exception at some point, the subscription is cancelled, and the exception is rethrown from
 * [collect]. Also, if the publisher signals an error, that error is rethrown from [collect].
 */
public suspend inline fun <T> JFlow.Publisher<T>.collect(action: (T) -> Unit): Unit =
    FlowAdapters.toPublisher(this).collect(action)
