/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.channels.Channel.Factory.BUFFERED
import kotlinx.coroutines.channels.Channel.Factory.OPTIONAL_CHANNEL
import kotlinx.coroutines.flow.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * Represents the given broadcast channel as a hot flow.
 * Every flow collector will trigger a new broadcast channel subscription.
 *
 * ### Cancellation semantics
 * 1) Flow consumer is cancelled when the original channel is cancelled.
 * 2) Flow consumer completes normally when the original channel completes (~is closed) normally.
 * 3) If the flow consumer fails with an exception, subscription is cancelled.
 */
@FlowPreview
public fun <T> BroadcastChannel<T>.asFlow(): Flow<T> = flow {
    val subscription = openSubscription()
    subscription.consumeEach { value ->
        emit(value)
    }
}

/**
 * Creates a [broadcast] coroutine that collects the given flow.
 *
 * This transformation is **stateful**, it launches a [broadcast] coroutine
 * that collects the given flow and thus resulting channel should be properly closed or cancelled.
 *
 * A channel with [default][Channel.Factory.BUFFERED] buffer size is created.
 * Use [buffer] operator on the flow before calling `produce` to specify a value other than
 * default and to control what happens when data is produced faster than it is consumed,
 * that is to control backpressure behavior.
 */
@FlowPreview
public fun <T> Flow<T>.broadcastIn(
    scope: CoroutineScope,
    start: CoroutineStart = CoroutineStart.LAZY
): BroadcastChannel<T> =
    asChannelFlow().broadcastImpl(scope, start)

/**
 * Creates a [produce] coroutine that collects the given flow.
 *
 * This transformation is **stateful**, it launches a [produce] coroutine
 * that collects the given flow and thus resulting channel should be properly closed or cancelled.
 *
 * A channel with [default][Channel.Factory.BUFFERED] buffer size is created.
 * Use [buffer] operator on the flow before calling `produce` to specify a value other than
 * default and to control what happens when data is produced faster than it is consumed,
 * that is to control backpressure behavior.
 */
@FlowPreview
public fun <T> Flow<T>.produceIn(
    scope: CoroutineScope
): ReceiveChannel<T> =
    asChannelFlow().produceImpl(scope)
