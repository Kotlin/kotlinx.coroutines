/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("UNCHECKED_CAST", "NON_APPLICABLE_CALL_FOR_BUILDER_INFERENCE") // KT-32203

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*

internal fun getNull(): Symbol = NULL // Workaround for JS BE bug

internal suspend fun <T1, T2, R> FlowCollector<R>.combineTransformInternal(
    first: Flow<T1>, second: Flow<T2>,
    transform: suspend FlowCollector<R>.(a: T1, b: T2) -> Unit
) {
    coroutineScope {
        val firstChannel = asFairChannel(first)
        val secondChannel = asFairChannel(second)
        var firstValue: Any? = null
        var secondValue: Any? = null
        var firstIsClosed = false
        var secondIsClosed = false
        while (!firstIsClosed || !secondIsClosed) {
            select<Unit> {
                onReceive(firstIsClosed, firstChannel, { firstIsClosed = true }) { value ->
                    firstValue = value
                    if (secondValue !== null) {
                        transform(getNull().unbox(firstValue), getNull().unbox(secondValue) as T2)
                    }
                }

                onReceive(secondIsClosed, secondChannel, { secondIsClosed = true }) { value ->
                    secondValue = value
                    if (firstValue !== null) {
                        transform(getNull().unbox(firstValue) as T1, getNull().unbox(secondValue) as T2)
                    }
                }
            }
        }
    }
}

@PublishedApi
internal suspend fun <R, T> FlowCollector<R>.combineInternal(
    flows: Array<out Flow<T>>,
    arrayFactory: () -> Array<T?>,
    transform: suspend FlowCollector<R>.(Array<T>) -> Unit
): Unit = coroutineScope {
    val size = flows.size
    val channels = Array(size) { asFairChannel(flows[it]) }
    val latestValues = arrayOfNulls<Any?>(size)
    val isClosed = Array(size) { false }
    var nonClosed = size
    var remainingNulls = size
    // See flow.combine(other) for explanation.
    while (nonClosed != 0) {
        select<Unit> {
            for (i in 0 until size) {
                onReceive(isClosed[i], channels[i], { isClosed[i] = true; --nonClosed }) { value ->
                    if (latestValues[i] == null) --remainingNulls
                    latestValues[i] = value
                    if (remainingNulls != 0) return@onReceive
                    val arguments = arrayFactory()
                    for (index in 0 until size) {
                        arguments[index] = NULL.unbox(latestValues[index])
                    }
                    transform(arguments as Array<T>)
                }
            }
        }
    }
}

private inline fun SelectBuilder<Unit>.onReceive(
    isClosed: Boolean,
    channel: ReceiveChannel<Any>,
    crossinline onClosed: () -> Unit,
    noinline onReceive: suspend (value: Any) -> Unit
) {
    if (isClosed) return
    @Suppress("DEPRECATION")
    channel.onReceiveOrNull {
        // TODO onReceiveOrClosed when boxing issues are fixed
        if (it === null) onClosed()
        else onReceive(it)
    }
}

// Channel has any type due to onReceiveOrNull. This will be fixed after receiveOrClosed
private fun CoroutineScope.asFairChannel(flow: Flow<*>): ReceiveChannel<Any> = produce {
    val channel = channel as ChannelCoroutine<Any>
    flow.collect { value ->
        return@collect channel.sendFair(value ?: NULL)
    }
}

internal fun <T1, T2, R> zipImpl(flow: Flow<T1>, flow2: Flow<T2>, transform: suspend (T1, T2) -> R): Flow<R> = unsafeFlow {
    coroutineScope {
        val first = asChannel(flow)
        val second = asChannel(flow2)
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
        (second as SendChannel<*>).invokeOnClose {
            if (!first.isClosedForReceive) first.cancel(AbortFlowException(this@unsafeFlow))
        }

        val otherIterator = second.iterator()
        try {
            first.consumeEach { value ->
                if (!otherIterator.hasNext()) {
                    return@consumeEach
                }
                emit(transform(NULL.unbox(value), NULL.unbox(otherIterator.next())))
            }
        } catch (e: AbortFlowException) {
            e.checkOwnership(owner = this@unsafeFlow)
        } finally {
            if (!second.isClosedForReceive) second.cancel(AbortFlowException(this@unsafeFlow))
        }
    }
}

// Channel has any type due to onReceiveOrNull. This will be fixed after receiveOrClosed
private fun CoroutineScope.asChannel(flow: Flow<*>): ReceiveChannel<Any> = produce {
    flow.collect { value ->
        return@collect channel.send(value ?: NULL)
    }
}
