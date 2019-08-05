/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.Channel.Factory.BUFFERED
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.flow.internal.unsafeFlow as flow
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * Creates a flow from the given suspendable [block].
 *
 * Example of usage:
 * ```
 * fun fibonacci(): Flow<BigInteger> = flow {
 *     var x = BigInteger.ZERO
 *     var y = BigInteger.ONE
 *     while (true) {
 *         emit(x)
 *         x = y.also {
 *             y += x
 *         }
 *     }
 * }
 *
 * fibonacci().take(100).collect { println(it) }
 * ```
 *
 * `emit` should happen strictly in the dispatchers of the [block] in order to preserve the flow context.
 * For example, the following code will result in an [IllegalStateException]:
 * ```
 * flow {
 *     emit(1) // Ok
 *     withContext(Dispatcher.IO) {
 *         emit(2) // Will fail with ISE
 *     }
 * }
 * ```
 * If you want to switch the context of execution of a flow, use the [flowOn] operator.
 */
public fun <T> flow(@BuilderInference block: suspend FlowCollector<T>.() -> Unit): Flow<T> = SafeFlow(block)

// Named anonymous object
private class SafeFlow<T>(private val block: suspend FlowCollector<T>.() -> Unit) : Flow<T> {
    override suspend fun collect(collector: FlowCollector<T>) {
        SafeCollector(collector, coroutineContext).block()
    }
}

/**
 * Creates a flow that produces a single value from the given functional type.
 */
@FlowPreview
public fun <T> (() -> T).asFlow(): Flow<T> = flow {
    emit(invoke())
}

/**
 * Creates a flow that produces a single value from the given functional type.
 * Example of usage:
 * ```
 * suspend fun remoteCall(): R = ...
 * fun remoteCallFlow(): Flow<R> = ::remoteCall.asFlow()
 * ```
 */
@FlowPreview
public fun <T> (suspend () -> T).asFlow(): Flow<T> = flow {
    emit(invoke())
}

/**
 * Creates a flow that produces values from the given iterable.
 */
public fun <T> Iterable<T>.asFlow(): Flow<T> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a flow that produces values from the given iterator.
 */
public fun <T> Iterator<T>.asFlow(): Flow<T> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a flow that produces values from the given sequence.
 */
public fun <T> Sequence<T>.asFlow(): Flow<T> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a flow that produces values from the specified `vararg`-arguments.
 *
 * Example of usage:
 * ```
 * flowOf(1, 2, 3)
 * ```
 */
public fun <T> flowOf(vararg elements: T): Flow<T> = flow {
    for (element in elements) {
        emit(element)
    }
}

/**
 * Creates flow that produces the given [value].
 */
public fun <T> flowOf(value: T): Flow<T> = flow {
    /*
     * Implementation note: this is just an "optimized" overload of flowOf(vararg)
     * which significantly reduces the footprint of widespread single-value flows.
     */
    emit(value)
}

/**
 * Returns an empty flow.
 */
public fun <T> emptyFlow(): Flow<T> = EmptyFlow

private object EmptyFlow : Flow<Nothing> {
    override suspend fun collect(collector: FlowCollector<Nothing>) = Unit
}

/**
 * Creates a flow that produces values from the given array.
 */
public fun <T> Array<T>.asFlow(): Flow<T> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a flow that produces values from the array.
 */
public fun IntArray.asFlow(): Flow<Int> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a flow that produces values from the array.
 */
public fun LongArray.asFlow(): Flow<Long> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a flow that produces values from the range.
 */
public fun IntRange.asFlow(): Flow<Int> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a flow that produces values from the range.
 */
public fun LongRange.asFlow(): Flow<Long> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * @suppress
 */
@FlowPreview
@Deprecated(
    message = "Use channelFlow with awaitClose { } instead of flowViaChannel and invokeOnClose { }.",
    level = DeprecationLevel.WARNING
)
@Suppress("DeprecatedCallableAddReplaceWith")
public fun <T> flowViaChannel(
    bufferSize: Int = BUFFERED,
    @BuilderInference block: CoroutineScope.(channel: SendChannel<T>) -> Unit
): Flow<T> {
    return channelFlow<T> {
        block(channel)
        awaitClose()
    }.buffer(bufferSize)
}

/**
 * Creates an instance of the cold [Flow] with elements that are sent to a [SendChannel]
 * provided to the builder's [block] of code via [ProducerScope]. It allows elements to be
 * produced by code that is running in a different context or concurrently.
 * The resulting flow is _cold_, which means that [block] is called every time a terminal operator
 * is applied to the resulting flow.
 *
 * This builder ensures thread-safety and context preservation, thus the provided [ProducerScope] can be used
 * concurrently from different contexts.
 * The resulting flow completes as soon as the code in the [block] and all its children completes.
 * Use [awaitClose] as the last statement to keep it running.
 * A more detailed example is provided in the documentation of [callbackFlow].
 *
 * A channel with the [default][Channel.BUFFERED] buffer size is used. Use the [buffer] operator on the
 * resulting flow to specify a user-defined value and to control what happens when data is produced faster
 * than consumed, i.e. to control the back-pressure behavior.
 *
 * Adjacent applications of [channelFlow], [flowOn], [buffer], [produceIn], and [broadcastIn] are
 * always fused so that only one properly configured channel is used for execution.
 *
 * Examples of usage:
 *
 * ```
 * fun <T> Flow<T>.merge(other: Flow<T>): Flow<T> = channelFlow {
 *     // collect from one coroutine and send it
 *     launch {
 *         collect { send(it) }
 *     }
 *     // collect and send from this coroutine, too, concurrently
 *     other.collect { send(it) }
 * }
 *
 * fun <T> contextualFlow(): Flow<T> = channelFlow {
 *     // send from one coroutine
 *     launch(Dispatchers.IO) {
 *         send(computeIoValue())
 *     }
 *     // send from another coroutine, concurrently
 *     launch(Dispatchers.Default) {
 *         send(computeCpuValue())
 *     }
 * }
 * ```
 */
@ExperimentalCoroutinesApi
public fun <T> channelFlow(@BuilderInference block: suspend ProducerScope<T>.() -> Unit): Flow<T> =
    ChannelFlowBuilder(block)

/**
 * Creates an instance of the cold [Flow] with elements that are sent to a [SendChannel]
 * provided to the builder's [block] of code via [ProducerScope]. It allows elements to be
 * produced by code that is running in a different context or concurrently.
 *
 * The resulting flow is _cold_, which means that [block] is called every time a terminal operator
 * is applied to the resulting flow.
 *
 * This builder ensures thread-safety and context preservation, thus the provided [ProducerScope] can be used
 * from any context, e.g. from a callback-based API.
 * The resulting flow completes as soon as the code in the [block] and all its children completes.
 * Use [awaitClose] as the last statement to keep it running.
 * The [awaitClose] argument is called either when a flow consumer cancels the flow collection
 * or when a callback-based API invokes [SendChannel.close] manually.
 *
 * A channel with the [default][Channel.BUFFERED] buffer size is used. Use the [buffer] operator on the
 * resulting flow to specify a user-defined value and to control what happens when data is produced faster
 * than consumed, i.e. to control the back-pressure behavior.
 *
 * Adjacent applications of [callbackFlow], [flowOn], [buffer], [produceIn], and [broadcastIn] are
 * always fused so that only one properly configured channel is used for execution.
 *
 * Example of usage:
 *
 * ```
 * fun flowFrom(api: CallbackBasedApi): Flow<T> = callbackFlow {
 *     val callback = object : Callback { // implementation of some callback interface
 *         override fun onNextValue(value: T) {
 *             // Note: offer drops value when buffer is full
 *             // Use either buffer(Channel.CONFLATED) or buffer(Channel.UNLIMITED) to avoid overfill
 *             offer(value)
 *         }
 *         override fun onApiError(cause: Throwable) {
 *             cancel(CancellationException("API Error", cause))
 *         }
 *         override fun onCompleted() = channel.close()
 *     }
 *     api.register(callback)
 *     // Suspend until either onCompleted or external cancellation are invoked
 *     awaitClose { api.unregister(callback) }
 * }
 * ```
 */
@Suppress("NOTHING_TO_INLINE")
@ExperimentalCoroutinesApi
public inline fun <T> callbackFlow(@BuilderInference noinline block: suspend ProducerScope<T>.() -> Unit): Flow<T> =
    channelFlow(block)

// ChannelFlow implementation that is the first in the chain of flow operations and introduces (builds) a flow
private class ChannelFlowBuilder<T>(
    private val block: suspend ProducerScope<T>.() -> Unit,
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = BUFFERED
) : ChannelFlow<T>(context, capacity) {
    override fun create(context: CoroutineContext, capacity: Int): ChannelFlow<T> =
        ChannelFlowBuilder(block, context, capacity)

    override suspend fun collectTo(scope: ProducerScope<T>) =
        block(scope)

    override fun toString(): String =
        "block[$block] -> ${super.toString()}"
}
