/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * Creates a flow from the given suspendable [block].
 *
 * Example of usage:
 * ```
 * fun fibonacci(): Flow<Long> = flow {
 *     emit(1L)
 *     var f1 = 1L
 *     var f2 = 1L
 *     repeat(100) {
 *         var tmp = f1
 *         f1 = f2
 *         f2 += tmp
 *         emit(f1)
 *     }
 * }
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
@FlowPreview
public fun <T> flow(@BuilderInference block: suspend FlowCollector<T>.() -> Unit): Flow<T> {
    return object : Flow<T> {
        override suspend fun collect(collector: FlowCollector<T>) {
            SafeCollector(collector, coroutineContext).block()
        }
    }
}

/**
 * An analogue of the [flow] builder that does not check the context of execution of the resulting flow.
 * Used in our own operators where we trust the context of invocations.
 */
@FlowPreview
@PublishedApi
internal inline fun <T> unsafeFlow(@BuilderInference crossinline block: suspend FlowCollector<T>.() -> Unit): Flow<T> {
    return object : Flow<T> {
        override suspend fun collect(collector: FlowCollector<T>) {
            collector.block()
        }
    }
}

/**
 * Creates a flow that produces a single value from the given functional type.
 */
@FlowPreview
public fun <T> (() -> T).asFlow(): Flow<T> = unsafeFlow {
    emit(invoke())
}

/**
 * Creates a flow that produces a single value from the given functional type.
 * Example of usage:
 * ```
 * suspend fun remoteCall(): R = ...
 * suspend fun remoteCallFlow(): Flow<R> = ::remoteCall.asFlow()
 * ```
 */
@FlowPreview
public fun <T> (suspend () -> T).asFlow(): Flow<T> = unsafeFlow {
    emit(invoke())
}

/**
 * Creates a flow that produces values from the given iterable.
 */
@FlowPreview
public fun <T> Iterable<T>.asFlow(): Flow<T> = unsafeFlow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a flow that produces values from the given iterable.
 */
@FlowPreview
public fun <T> Iterator<T>.asFlow(): Flow<T> = unsafeFlow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a flow that produces values from the given sequence.
 */
@FlowPreview
public fun <T> Sequence<T>.asFlow(): Flow<T> = unsafeFlow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a flow that produces values from the given array of elements.
 */
@FlowPreview
public fun <T> flowOf(vararg elements: T): Flow<T> = unsafeFlow {
    for (element in elements) {
        emit(element)
    }
}

/**
 * Creates flow that produces a given [value].
 */
@FlowPreview
public fun <T> flowOf(value: T): Flow<T> = unsafeFlow {
    /*
     * Implementation note: this is just an "optimized" overload of flowOf(vararg)
     * which significantly reduce the footprint of widespread single-value flows.
     */
    emit(value)
}

/**
 * Returns an empty flow.
 */
@FlowPreview
public fun <T> emptyFlow(): Flow<T> = EmptyFlow

private object EmptyFlow : Flow<Nothing> {
    override suspend fun collect(collector: FlowCollector<Nothing>) = Unit
}

/**
 * Creates a flow that produces values from the given array.
 */
@FlowPreview
public fun <T> Array<T>.asFlow(): Flow<T> = unsafeFlow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given array.
 */
@FlowPreview
public fun IntArray.asFlow(): Flow<Int> = unsafeFlow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given array.
 */
@FlowPreview
public fun LongArray.asFlow(): Flow<Long> = unsafeFlow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given range.
 */
@FlowPreview
public fun IntRange.asFlow(): Flow<Int> = unsafeFlow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates flow that produces values from the given range.
 */
@FlowPreview
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
    message = "Use channelFlow instead",
    level = DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("channelFlow(bufferSize, block)")
)
public fun <T> flowViaChannel(
    bufferSize: Int = 16,
    @BuilderInference block: CoroutineScope.(channel: SendChannel<T>) -> Unit
): Flow<T> {
    return flow {
        coroutineScope {
            val channel = Channel<T>(bufferSize)
            launch {
                block(channel)
            }

            channel.consumeEach { value ->
                emit(value)
            }
        }
    }
}

/**
 * Creates an instance of the cold [Flow] with elements that are sent to a [SendChannel]
 * that is provided to the builder's [block] of code via [ProducerScope]. It allows elements to be
 * produced by the code that is running in a different context or running concurrently.
 * The resulting flow is _cold_, which means that [block] is called on each call of a terminal operator
 * on the resulting flow.
 *
 * This builder ensures thread-safety and context preservation, thus the provided [ProducerScope] can be used concurrently from different contexts.
 * The resulting flow will complete as soon as [ProducerScope], to artificially prolong it [awaitClose] can be used.
 * For more detailed example please refer to [callbackFlow] documentation.
 *
 * To control backpressure, [bufferSize] is used and matches directly the `capacity` parameter of [Channel] factory.
 * The provided channel can later be used by any external service to communicate with the flow and its buffer determines
 * backpressure buffer size or its behaviour (e.g. in the case when [Channel.CONFLATED] was used).
 *
 * Examples of usage:
 * ```
 * fun <T> Flow<T>.merge(other: Flow<T>): Flow<T> = channelFlow {
 *     launch {
 *         collect { value -> send(value) }
 *     }
 *     other.collect { value -> send(value) }
 * }
 *
 * fun <T> contextualFlow(): Flow<T> = channelFlow {
 *     launch(Dispatchers.IO) {
 *         send(computeIoValue())
 *     }
 *
 *     launch(Dispatchers.Default) {
 *         send(computeCpuValue())
 *     }
 * }
 * ```
 */
@FlowPreview
public fun <T> channelFlow(bufferSize: Int = 16, @BuilderInference block: suspend ProducerScope<T>.() -> Unit): Flow<T> =
    flow {
        coroutineScope {
            val channel = produce(capacity = bufferSize, block = block)
            channel.consumeEach { value ->
                emit(value)
            }
        }
    }

/**
 * Creates an instance of the cold [Flow] with elements that are sent to a [SendChannel]
 * that is provided to the builder's [block] of code via [ProducerScope]. It allows elements to be
 * produced by the code that is running in a different context or running concurrently.
 *
 * The resulting flow is _cold_, which means that [block] is called on each call of a terminal operator
 * on the resulting flow.
 *
 * This builder ensures thread-safety and context preservation, thus the provided [ProducerScope] can be used from any context,
 * e.g. from the callback-based API. The flow completes as soon as its scope completes, thus if you are using channel from the
 * callback-based API, to artificially prolong scope lifetime and avoid memory-leaks related to unregistered resources,
 * [awaitClose] extension should be used. [awaitClose] argument will be invoked when either flow consumer cancels flow collection
 * or when callback-based API invokes [SendChannel.close] manually.
 *
 * To control backpressure, [bufferSize] is used and matches directly the `capacity` parameter of [Channel] factory.
 * The provided channel can later be used by any external service to communicate with the flow and its buffer determines
 * backpressure buffer size or its behaviour (e.g. in the case when [Channel.CONFLATED] was used).
 *
 * Example of usage:
 * ```
 * fun flowFrom(api: CallbackBasedApi): Flow<T> = callbackFlow {
 *     val callback = object : Callback { // implementation of some callback interface
 *         override fun onNextValue(value: T) {
 *             // Note: offer drops value when buffer is full
 *             // Channel.UNLIMITED can be used to avoid overfill
 *             offer(value)
 *         }
 *         override fun onApiError(cause: Throwable) {
 *             cancel(CancellationException("API Error", cause))
 *         }
 *         override fun onCompleted() = channel.close()
 *     }
 *     api.register(callback)
 *     // Suspend until either onCompleted or external cancellation are invoked
 *     await { api.unregister(callback) }
 * }
 * ```
 */
public inline fun <T> callbackFlow(bufferSize: Int = 16, @BuilderInference crossinline block: suspend ProducerScope<T>.() -> Unit): Flow<T> =
    channelFlow(bufferSize) { block() }
