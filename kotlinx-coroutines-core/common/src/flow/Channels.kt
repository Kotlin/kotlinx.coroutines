/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.internal.unsafeFlow as flow

/**
 * Emits all elements from the given [channel] to this flow collector and [cancels][cancel] (consumes)
 * the channel afterwards. If you need to iterate over the channel without consuming it,
 * a regular `for` loop should be used instead.
 *
 * Note, that emitting values from a channel into a flow is not atomic. A value that was received from the
 * channel many not reach the flow collector if it was cancelled and will be lost.
 *
 * This function provides a more efficient shorthand for `channel.consumeEach { value -> emit(value) }`.
 * See [consumeEach][ReceiveChannel.consumeEach].
 */
public suspend fun <T> FlowCollector<T>.emitAll(channel: ReceiveChannel<T>): Unit =
    emitAllImpl(channel, consume = true)

private suspend fun <T> FlowCollector<T>.emitAllImpl(channel: ReceiveChannel<T>, consume: Boolean) {
    ensureActive()
    var cause: Throwable? = null
    try {
        for (element in channel) {
            emit(element)
        }
    } catch (e: Throwable) {
        cause = e
        throw e
    } finally {
        if (consume) channel.cancelConsumed(cause)
    }
}

/**
 * Represents the given receive channel as a hot flow and [receives][ReceiveChannel.receive] from the channel
 * in fan-out fashion every time this flow is collected. One element will be emitted to one collector only.
 *
 * See also [consumeAsFlow] which ensures that the resulting flow is collected just once.
 *
 * ### Cancellation semantics
 *
 * * Flow collectors are cancelled when the original channel is [closed][SendChannel.close] with an exception.
 * * Flow collectors complete normally when the original channel is [closed][SendChannel.close] normally.
 * * Failure or cancellation of the flow collector does not affect the channel.
 *
 * ### Operator fusion
 *
 * Adjacent applications of [flowOn], [buffer], [conflate], and [produceIn] to the result of `receiveAsFlow` are fused.
 * In particular, [produceIn] returns the original channel.
 * Calls to [flowOn] have generally no effect, unless [buffer] is used to explicitly request buffering.
 */
public fun <T> ReceiveChannel<T>.receiveAsFlow(): Flow<T> = ChannelAsFlow(this, consume = false)

/**
 * Represents the given receive channel as a hot flow and [consumes][ReceiveChannel.consume] the channel
 * on the first collection from this flow. The resulting flow can be collected just once and throws
 * [IllegalStateException] when trying to collect it more than once.
 *
 * See also [receiveAsFlow] which supports multiple collectors of the resulting flow.
 *
 * ### Cancellation semantics
 *
 * * Flow collector is cancelled when the original channel is [closed][SendChannel.close] with an exception.
 * * Flow collector completes normally when the original channel is [closed][SendChannel.close] normally.
 * * If the flow collector fails with an exception, the source channel is [cancelled][ReceiveChannel.cancel].
 *
 * ### Operator fusion
 *
 * Adjacent applications of [flowOn], [buffer], [conflate], and [produceIn] to the result of `consumeAsFlow` are fused.
 * In particular, [produceIn] returns the original channel (but throws [IllegalStateException] on repeated calls).
 * Calls to [flowOn] have generally no effect, unless [buffer] is used to explicitly request buffering.
 */
public fun <T> ReceiveChannel<T>.consumeAsFlow(): Flow<T> = ChannelAsFlow(this, consume = true)

/**
 * Represents an existing [channel] as [ChannelFlow] implementation.
 * It fuses with subsequent [flowOn] operators, but for the most part ignores the specified context.
 * However, additional [buffer] calls cause a separate buffering channel to be created and that is where
 * the context might play a role, because it is used by the producing coroutine.
 */
private class ChannelAsFlow<T>(
    private val channel: ReceiveChannel<T>,
    private val consume: Boolean,
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = Channel.OPTIONAL_CHANNEL,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND
) : ChannelFlow<T>(context, capacity, onBufferOverflow) {
    private val consumed = atomic(false)

    private fun markConsumed() {
        if (consume) {
            check(!consumed.getAndSet(true)) { "ReceiveChannel.consumeAsFlow can be collected just once" }
        }
    }
    
    override fun create(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow): ChannelFlow<T> =
        ChannelAsFlow(channel, consume, context, capacity, onBufferOverflow)

    override fun dropChannelOperators(): Flow<T> =
        ChannelAsFlow(channel, consume)

    override suspend fun collectTo(scope: ProducerScope<T>) =
        SendingCollector(scope).emitAllImpl(channel, consume) // use efficient channel receiving code from emitAll

    override fun produceImpl(scope: CoroutineScope): ReceiveChannel<T> {
        markConsumed() // fail fast on repeated attempt to collect it
        return if (capacity == Channel.OPTIONAL_CHANNEL) {
            channel // direct
        } else
            super.produceImpl(scope) // extra buffering channel
    }

    override suspend fun collect(collector: FlowCollector<T>) {
        if (capacity == Channel.OPTIONAL_CHANNEL) {
            markConsumed()
            collector.emitAllImpl(channel, consume) // direct
        } else {
            super.collect(collector) // extra buffering channel, produceImpl will mark it as consumed
        }
    }

    override fun additionalToStringProps(): String = "channel=$channel"
}

/**
 * Represents the given broadcast channel as a hot flow.
 * Every flow collector will trigger a new broadcast channel subscription.
 *
 * ### Cancellation semantics
 * 1) Flow consumer is cancelled when the original channel is cancelled.
 * 2) Flow consumer completes normally when the original channel completes (~is closed) normally.
 * 3) If the flow consumer fails with an exception, subscription is cancelled.
 */
@Deprecated(
    level = DeprecationLevel.WARNING,
    message = "'BroadcastChannel' is obsolete and all corresponding operators are deprecated " +
        "in the favour of StateFlow and SharedFlow"
) // Since 1.5.0, was @FlowPreview, safe to remove in 1.7.0
public fun <T> BroadcastChannel<T>.asFlow(): Flow<T> = flow {
    emitAll(openSubscription())
}

/**
 * Creates a [produce] coroutine that collects the given flow.
 *
 * This transformation is **stateful**, it launches a [produce] coroutine
 * that collects the given flow, and has the same behavior:
 *
 * * if collecting the flow throws, the channel will be closed with that exception
 * * if the [ReceiveChannel] is cancelled, the collection of the flow will be cancelled
 * * if collecting the flow completes normally, the [ReceiveChannel] will be closed normally
 *
 * A channel with [default][Channel.Factory.BUFFERED] buffer size is created.
 * Use [buffer] operator on the flow before calling `produceIn` to specify a value other than
 * default and to control what happens when data is produced faster than it is consumed,
 * that is to control backpressure behavior.
 */
public fun <T> Flow<T>.produceIn(
    scope: CoroutineScope
): ReceiveChannel<T> =
    asChannelFlow().produceImpl(scope)
