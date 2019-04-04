/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
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
 */
@FlowPreview
public fun <T> Flow<T>.broadcastIn(
    scope: CoroutineScope, capacity: Int = 1,
    start: CoroutineStart = CoroutineStart.LAZY
): BroadcastChannel<T> = scope.broadcast(capacity = capacity, start = start) {
    collect { value ->
        send(value)
    }
}

/**
 * Creates a [produce] coroutine that collects the given flow.
 *
 * This transformation is **stateful**, it launches a [produce] coroutine
 * that collects the given flow and thus resulting channel should be properly closed or cancelled.
 */
@FlowPreview
public fun <T> Flow<T>.produceIn(
    scope: CoroutineScope,
    capacity: Int = 1
): ReceiveChannel<T> = scope.produce(capacity = capacity) {
    // TODO it would be nice to have it with start = lazy as well
    collect { value ->
        send(value)
    }
}
