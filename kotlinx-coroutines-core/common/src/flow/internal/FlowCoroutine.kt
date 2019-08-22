/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlinx.coroutines.flow.internal.unsafeFlow as flow

/**
 * Creates a [CoroutineScope] and calls the specified suspend block with this scope.
 * This builder is similar to [coroutineScope] with the only exception that it *ties* lifecycle of children
 * and itself regarding the cancellation, thus being cancelled when one of the children becomes cancelled.
 *
 * For example:
 * ```
 * flowScope {
 *     launch {
 *         throw CancellationException()
 *     }
 * } // <- CE will be rethrown here
 * ```
 */
internal suspend fun <R> flowScope(@BuilderInference block: suspend CoroutineScope.() -> R): R =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val coroutine = FlowCoroutine(uCont.context, uCont)
        coroutine.startUndispatchedOrReturn(coroutine, block)
    }

/**
 * Creates a flow that also provides a [CoroutineScope] for each collector
 * Shorthand for:
 * ```
 * flow {
 *     flowScope {
 *         ...
 *     }
 * }
 * ```
 * with additional constraint on cancellation.
 * To cancel child without cancelling itself, `cancel(ChildCancelledException())` should be used.
 */
internal fun <R> scopedFlow(@BuilderInference block: suspend CoroutineScope.(FlowCollector<R>) -> Unit): Flow<R> =
    flow {
        val collector = this
        flowScope { block(collector) }
    }

internal fun <T> CoroutineScope.flowProduce(
    context: CoroutineContext,
    capacity: Int = 0,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): ReceiveChannel<T> {
    val channel = Channel<T>(capacity)
    val newContext = newCoroutineContext(context)
    val coroutine = FlowProduceCoroutine(newContext, channel)
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
    return coroutine
}

private class FlowCoroutine<T>(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {
    public override fun childCancelled(cause: Throwable): Boolean {
        if (cause is ChildCancelledException) return true
        return cancelImpl(cause)
    }
}

private class FlowProduceCoroutine<T>(
    parentContext: CoroutineContext,
    channel: Channel<T>
) : ProducerCoroutine<T>(parentContext, channel) {
    public override fun childCancelled(cause: Throwable): Boolean {
        if (cause is ChildCancelledException) return true
        return cancelImpl(cause)
    }
}
