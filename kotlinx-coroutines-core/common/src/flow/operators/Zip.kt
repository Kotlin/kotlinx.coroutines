/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")
@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.selects.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.unsafeFlow as flow

/**
 * Returns a [Flow] whose values are generated with [transform] function by combining
 * the most recently emitted values by each flow.
 *
 * It can be demonstrated with the following example:
 * ```
 * val flow = flowOf(1, 2).delayEach(10)
 * val flow2 = flowOf("a", "b", "c").delayEach(15)
 * flow.combineLatest(flow2) { i, s -> i.toString() + s }.collect {
 *     println(it) // Will print "1a 2a 2b 2c"
 * }
 * ```
 */
public fun <T1, T2, R> Flow<T1>.combineLatest(other: Flow<T2>, transform: suspend (T1, T2) -> R): Flow<R> = flow {
    coroutineScope {
        val firstChannel = asFairChannel(this@combineLatest)
        val secondChannel = asFairChannel(other)
        var firstValue: Any? = null
        var secondValue: Any? = null
        var firstIsClosed = false
        var secondIsClosed = false

        /*
         * Fun fact, this select **semantically** equivalent of the following:
         * ```
         * selectWhile<Unit> {
         *     channel.onReceive {
         *         emitCombined(...)
         *     }
         *     channel2.onReceive {
         *         emitCombined(...)
         *     }
         * }
         * ```
         * but we are waiting for `channels` branch to get merged where we will change semantics of the select
         * to ignore finished clauses.
         *
         * Instead (especially in the face of non-fair channels) we are using our own hand-rolled select emulation
         * on top of previous select.
         */
        while (!firstIsClosed || !secondIsClosed) {
            select<Unit> {
                onReceive(firstIsClosed, firstChannel, { firstIsClosed = true }) { value ->
                    firstValue = value
                    if (secondValue !== null) {
                        emit(transform(NullSurrogate.unbox(firstValue), NullSurrogate.unbox(secondValue)))
                    }
                }

                onReceive(secondIsClosed, secondChannel, { secondIsClosed = true }) { value ->
                    secondValue = value
                    if (firstValue !== null) {
                        emit(transform(NullSurrogate.unbox(firstValue), NullSurrogate.unbox(secondValue)))
                    }
                }
            }
        }
    }
}


private inline fun SelectBuilder<Unit>.onReceive(
    isClosed: Boolean,
    channel: Channel<Any>,
    crossinline onClosed: () -> Unit,
    noinline onReceive: suspend (value: Any) -> Unit
) {
    if (isClosed) return
    channel.onReceiveOrNull {
        if (it === null) onClosed()
        else onReceive(it)
    }
}

// Channel has any type due to onReceiveOrNull. This will be fixed after receiveOrClosed
private fun CoroutineScope.asFairChannel(flow: Flow<*>): Channel<Any> {
    val channel = RendezvousChannel<Any>() // Explicit type
    launch {
        try {
            flow.collect { value ->
                channel.sendFair(value ?: NullSurrogate)
            }
        } finally {
            channel.close()
        }
    }
    return channel
}


/**
 * Zips values from the current flow (`this`) with [other] flow using provided [transform] function applied to each pair of values.
 * The resulting flow completes as soon as one of the flows completes and cancel is called on the remaining flow.
 *
 * It can be demonstrated with the following example:
 * ```
 * val flow = flowOf(1, 2, 3).delayEach(10)
 * val flow2 = flowOf("a", "b", "c", "d").delayEach(15)
 * flow.zip(flow2) { i, s -> i.toString() + s }.collect {
 *     println(it) // Will print "1a 2b 3c"
 * }
 * ```
 */
public fun <T1, T2, R> Flow<T1>.zip(other: Flow<T2>, transform: suspend (T1, T2) -> R): Flow<R> = flow {
    coroutineScope {
        val first = asChannel(this@zip)
        val second = asChannel(other)
        /*
         * This approach only works with rendezvous channel and is required to enforce correctness
         * in the following scenario:
         * ```
         * val f1 = flow { emit(1); delay(Long.MAX_VALUE) }
         * val f2 = flowOf(1)
         * f1.zip(f2) { ... }
         * ```
         *
         * Invariant: this clause is invoked only when all elements from the channel were processed (=> rendezvous restriction).
         */
        (second as SendChannel<*>).invokeOnClose { first.cancel() }

        val otherIterator = second.iterator()
        try {
            first.consumeEach { value ->
                if (!otherIterator.hasNext()) {
                    return@consumeEach
                }
                val secondValue = NullSurrogate.unbox<T2>(otherIterator.next())
                emit(transform(NullSurrogate.unbox(value), NullSurrogate.unbox(secondValue)))
            }
        } finally {
            second.cancel()
        }
    }
}

// Channel has any type due to onReceiveOrNull. This will be fixed after receiveOrClosed
private fun CoroutineScope.asChannel(flow: Flow<*>): ReceiveChannel<Any> = produce {
    flow.collect { value ->
        channel.send(value ?: NullSurrogate)
    }
}
