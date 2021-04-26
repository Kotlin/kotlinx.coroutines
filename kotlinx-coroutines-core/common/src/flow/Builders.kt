/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.Channel.Factory.BUFFERED
import kotlinx.coroutines.flow.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.internal.unsafeFlow as flow

/**
 * Creates a _cold_ flow from the given suspendable [block].
 * The flow being _cold_ means that the [block] is called every time a terminal operator is applied to the resulting flow.
 *
 * Example of usage:
 *
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
 * Emissions from [flow] builder are [cancellable] by default &mdash; each call to [emit][FlowCollector.emit]
 * also calls [ensureActive][CoroutineContext.ensureActive].
 *
 * `emit` should happen strictly in the dispatchers of the [block] in order to preserve the flow context.
 * For example, the following code will result in an [IllegalStateException]:
 *
 * ```
 * flow {
 *     emit(1) // Ok
 *     withContext(Dispatcher.IO) {
 *         emit(2) // Will fail with ISE
 *     }
 * }
 * ```
 *
 * If you want to switch the context of execution of a flow, use the [flowOn] operator.
 */
public fun <T> flow(@BuilderInference block: suspend FlowCollector<T>.() -> Unit): Flow<T> = SafeFlow(block)

// Named anonymous object
private class SafeFlow<T>(private val block: suspend FlowCollector<T>.() -> Unit) : AbstractFlow<T>() {
    override suspend fun collectSafely(collector: FlowCollector<T>) {
        collector.block()
    }
}

/**
 * Creates a _cold_ flow that produces a single value from the given functional type.
 */
@FlowPreview
public fun <T> (() -> T).asFlow(): Flow<T> = flow {
    emit(invoke())
}

/**
 * Creates a _cold_ flow that produces a single value from the given functional type.
 *
 * Example of usage:
 *
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
 * Creates a _cold_ flow that produces values from the given iterable.
 */
public fun <T> Iterable<T>.asFlow(): Flow<T> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a _cold_ flow that produces values from the given iterator.
 */
public fun <T> Iterator<T>.asFlow(): Flow<T> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a _cold_ flow that produces values from the given sequence.
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
 *
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
 * Creates a flow that produces the given [value].
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
 * Creates a _cold_ flow that produces values from the given array.
 * The flow being _cold_ means that the array components are read every time a terminal operator is applied
 * to the resulting flow.
 */
public fun <T> Array<T>.asFlow(): Flow<T> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a _cold_ flow that produces values from the array.
 * The flow being _cold_ means that the array components are read every time a terminal operator is applied
 * to the resulting flow.
 */
public fun IntArray.asFlow(): Flow<Int> = flow {
    forEach { value ->
        emit(value)
    }
}

/**
 * Creates a _cold_ flow that produces values from the given array.
 * The flow being _cold_ means that the array components are read every time a terminal operator is applied
 * to the resulting flow.
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
    level = DeprecationLevel.ERROR
) // To be removed in 1.4.x
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
 * Creates an instance of a _cold_ [Flow] with elements that are sent to a [SendChannel]
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
 * Adjacent applications of [channelFlow], [flowOn], [buffer], and [produceIn] are
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
public fun <T> channelFlow(@BuilderInference block: suspend ProducerScope<T>.() -> Unit): Flow<T> =
    ChannelFlowBuilder(block)

/**
 * Creates an instance of a _cold_ [Flow] with elements that are sent to a [SendChannel]
 * provided to the builder's [block] of code via [ProducerScope]. It allows elements to be
 * produced by code that is running in a different context or concurrently.
 *
 * The resulting flow is _cold_, which means that [block] is called every time a terminal operator
 * is applied to the resulting flow.
 *
 * This builder ensures thread-safety and context preservation, thus the provided [ProducerScope] can be used
 * from any context, e.g. from a callback-based API.
 * The resulting flow completes as soon as the code in the [block] completes.
 * [awaitClose] should be used to keep the flow running, otherwise the channel will be closed immediately
 * when block completes.
 * [awaitClose] argument is called either when a flow consumer cancels the flow collection
 * or when a callback-based API invokes [SendChannel.close] manually and is typically used
 * to cleanup the resources after the completion, e.g. unregister a callback.
 * Using [awaitClose] is mandatory in order to prevent memory leaks when the flow collection is cancelled,
 * otherwise the callback may keep running even when the flow collector is already completed.
 * To avoid such leaks, this method throws [IllegalStateException] if block returns, but the channel
 * is not closed yet.
 *
 * A channel with the [default][Channel.BUFFERED] buffer size is used. Use the [buffer] operator on the
 * resulting flow to specify a user-defined value and to control what happens when data is produced faster
 * than consumed, i.e. to control the back-pressure behavior.
 *
 * Adjacent applications of [callbackFlow], [flowOn], [buffer], and [produceIn] are
 * always fused so that only one properly configured channel is used for execution.
 *
 * Example of usage that converts a multi-shot callback API to a flow.
 * For single-shot callbacks use [suspendCancellableCoroutine].
 *
 * ```
 * fun flowFrom(api: CallbackBasedApi): Flow<T> = callbackFlow {
 *     val callback = object : Callback { // Implementation of some callback interface
 *         override fun onNextValue(value: T) {
 *             // To avoid blocking you can configure channel capacity using
 *             // either buffer(Channel.CONFLATED) or buffer(Channel.UNLIMITED) to avoid overfill
 *             trySendBlocking(value)
 *                 .onFailure { throwable ->
 *                     // Downstream has been cancelled or failed, can log here
 *                 }
 *         }
 *         override fun onApiError(cause: Throwable) {
 *             cancel(CancellationException("API Error", cause))
 *         }
 *         override fun onCompleted() = channel.close()
 *     }
 *     api.register(callback)
 *     /*
 *      * Suspends until either 'onCompleted'/'onApiError' from the callback is invoked
 *      * or flow collector is cancelled (e.g. by 'take(1)' or because a collector's coroutine was cancelled).
 *      * In both cases, callback will be properly unregistered.
 *      */
 *     awaitClose { api.unregister(callback) }
 * }
 * ```
 *
 * > The callback `register`/`unregister` methods provided by an external API must be thread-safe, because
 * > `awaitClose` block can be called at any time due to asynchronous nature of cancellation, even
 * > concurrently with the call of the callback.
 */
public fun <T> callbackFlow(@BuilderInference block: suspend ProducerScope<T>.() -> Unit): Flow<T> = CallbackFlowBuilder(block)

// ChannelFlow implementation that is the first in the chain of flow operations and introduces (builds) a flow
private open class ChannelFlowBuilder<T>(
    private val block: suspend ProducerScope<T>.() -> Unit,
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = BUFFERED,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND
) : ChannelFlow<T>(context, capacity, onBufferOverflow) {
    override fun create(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow): ChannelFlow<T> =
        ChannelFlowBuilder(block, context, capacity, onBufferOverflow)

    override suspend fun collectTo(scope: ProducerScope<T>) =
        block(scope)

    override fun toString(): String =
        "block[$block] -> ${super.toString()}"
}

private class CallbackFlowBuilder<T>(
    private val block: suspend ProducerScope<T>.() -> Unit,
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = BUFFERED,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND
) : ChannelFlowBuilder<T>(block, context, capacity, onBufferOverflow) {

    override suspend fun collectTo(scope: ProducerScope<T>) {
        super.collectTo(scope)
        /*
         * We expect user either call `awaitClose` from within a block (then the channel is closed at this moment)
         * or being closed/cancelled externally/manually. Otherwise "user forgot to call
         * awaitClose and receives unhelpful ClosedSendChannelException exceptions" situation is detected.
         */
        if (!scope.isClosedForSend) {
            throw IllegalStateException(
                """
                    'awaitClose { yourCallbackOrListener.cancel() }' should be used in the end of callbackFlow block.
                    Otherwise, a callback/listener may leak in case of external cancellation.
                    See callbackFlow API documentation for the details.
                """.trimIndent()
            )
        }
    }

    override fun create(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow): ChannelFlow<T> =
        CallbackFlowBuilder(block, context, capacity, onBufferOverflow)
}
