/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.Channel.Factory.BUFFERED
import kotlinx.coroutines.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.flow.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * Buffers flow emissions via channel of a specified capacity and runs collector in a separate coroutine.
 *
 * Normally, [flows][Flow] are _sequential_. It means that the code of all operators is executed in the
 * same coroutine. For example, consider the following code using [onEach] and [collect] operators:
 *
 * ```
 * flowOf("A", "B", "C")
 *     .onEach  { println("1$it") }
 *     .collect { println("2$it") }
 * ```
 *
 * It is going to be executed in the following order by the coroutine `Q` that calls this code:
 *
 * ```
 * Q : -->-- [1A] -- [2A] -- [1B] -- [2B] -- [1C] -- [2C] -->--
 * ```
 *
 * So if the operator's code takes considerable time to execute, then the total execution time is going to be
 * the sum of execution times for all operators.
 *
 * The `buffer` operator creates a separate coroutine during execution for the flow it applies to.
 * Consider the following code:
 *
 * ```
 * flowOf("A", "B", "C")
 *     .onEach  { println("1$it") }
 *     .buffer()  // <--------------- buffer between onEach and collect
 *     .collect { println("2$it") }
 * ```
 *
 * It will use two coroutines for execution of the code. A coroutine `Q` that calls this code is
 * going to execute `collect`, and the code before `buffer` will be executed in a separate
 * new coroutine `P` concurrently with `Q`:
 *
 * ```
 * P : -->-- [1A] -- [1B] -- [1C] ---------->--  // flowOf(...).onEach { ... }
 *
 *                       |
 *                       | channel               // buffer()
 *                       V
 *
 * Q : -->---------- [2A] -- [2B] -- [2C] -->--  // collect
 * ```
 *
 * When the operator's code takes some time to execute, this decreases the total execution time of the flow.
 * A [channel][Channel] is used between the coroutines to send elements emitted by the coroutine `P` to
 * the coroutine `Q`. If the code before `buffer` operator (in the coroutine `P`) is faster than the code after
 * `buffer` operator (in the coroutine `Q`), then this channel will become full at some point and will suspend
 * the producer coroutine `P` until the consumer coroutine `Q` catches up.
 * The [capacity] parameter defines the size of this buffer.
 *
 * ### Buffer overflow
 *
 * By default, the emitter is suspended when the buffer overflows, to let collector catch up. This strategy can be
 * overridden with an optional [onBufferOverflow] parameter so that the emitter is never suspended. In this
 * case, on buffer overflow either the oldest value in the buffer is dropped with the [DROP_OLDEST][BufferOverflow.DROP_OLDEST]
 * strategy and the latest emitted value is added to the buffer,
 * or the latest value that is being emitted is dropped with the [DROP_LATEST][BufferOverflow.DROP_LATEST] strategy,
 * keeping the buffer intact.
 * To implement either of the custom strategies, a buffer of at least one element is used.
 *
 * ### Operator fusion
 *
 * Adjacent applications of [channelFlow], [flowOn], [buffer], and [produceIn] are
 * always fused so that only one properly configured channel is used for execution.
 *
 * Explicitly specified buffer capacity takes precedence over `buffer()` or `buffer(Channel.BUFFERED)` calls,
 * which effectively requests a buffer of any size. Multiple requests with a specified buffer
 * size produce a buffer with the sum of the requested buffer sizes.
 *
 * A `buffer` call with a non-default value of the [onBufferOverflow] parameter overrides all immediately preceding
 * buffering operators, because it never suspends its upstream, and thus no upstream buffer would ever be used.
 *
 * ### Conceptual implementation
 *
 * The actual implementation of `buffer` is not trivial due to the fusing, but conceptually its basic
 * implementation is equivalent to the following code that can be written using [produce]
 * coroutine builder to produce a channel and [consumeEach][ReceiveChannel.consumeEach] extension to consume it:
 *
 * ```
 * fun <T> Flow<T>.buffer(capacity: Int = DEFAULT): Flow<T> = flow {
 *     coroutineScope { // limit the scope of concurrent producer coroutine
 *         val channel = produce(capacity = capacity) {
 *             collect { send(it) } // send all to channel
 *         }
 *         // emit all received values
 *         channel.consumeEach { emit(it) }
 *     }
 * }
 * ```
 *
 * ### Conflation
 *
 * Usage of this function with [capacity] of [Channel.CONFLATED][Channel.CONFLATED] is a shortcut to
 * `buffer(onBufferOverflow = `[`BufferOverflow.DROP_OLDEST`][BufferOverflow.DROP_OLDEST]`)`, and is available via
 * a separate [conflate] operator. See its documentation for details.
 *
 * @param capacity type/capacity of the buffer between coroutines. Allowed values are the same as in `Channel(...)`
 *   factory function: [BUFFERED][Channel.BUFFERED] (by default), [CONFLATED][Channel.CONFLATED],
 *   [RENDEZVOUS][Channel.RENDEZVOUS], [UNLIMITED][Channel.UNLIMITED] or a non-negative value indicating
 *   an explicitly requested size.
 * @param onBufferOverflow configures an action on buffer overflow (optional, defaults to
 *   [SUSPEND][BufferOverflow.SUSPEND], supported only when `capacity >= 0` or `capacity == Channel.BUFFERED`,
 *   implicitly creates a channel with at least one buffered element).
 */
@Suppress("NAME_SHADOWING")
public fun <T> Flow<T>.buffer(capacity: Int = BUFFERED, onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND): Flow<T> {
    require(capacity >= 0 || capacity == BUFFERED || capacity == CONFLATED) {
        "Buffer size should be non-negative, BUFFERED, or CONFLATED, but was $capacity"
    }
    require(capacity != CONFLATED || onBufferOverflow == BufferOverflow.SUSPEND) {
        "CONFLATED capacity cannot be used with non-default onBufferOverflow"
    }
    // desugar CONFLATED capacity to (0, DROP_OLDEST)
    var capacity = capacity
    var onBufferOverflow = onBufferOverflow
    if (capacity == CONFLATED) {
        capacity = 0
        onBufferOverflow = BufferOverflow.DROP_OLDEST
    }
    // create a flow
    return when (this) {
        is FusibleFlow -> fuse(capacity = capacity, onBufferOverflow = onBufferOverflow)
        else -> ChannelFlowOperatorImpl(this, capacity = capacity, onBufferOverflow = onBufferOverflow)
    }
}

@Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.4.0, binary compatibility with earlier versions")
public fun <T> Flow<T>.buffer(capacity: Int = BUFFERED): Flow<T> = buffer(capacity)

/**
 * Conflates flow emissions via conflated channel and runs collector in a separate coroutine.
 * The effect of this is that emitter is never suspended due to a slow collector, but collector
 * always gets the most recent value emitted.
 *
 * For example, consider the flow that emits integers from 1 to 30 with 100 ms delay between them:
 *
 * ```
 * val flow = flow {
 *     for (i in 1..30) {
 *         delay(100)
 *         emit(i)
 *     }
 * }
 * ```
 *
 * Applying `conflate()` operator to it allows a collector that delays 1 second on each element to get
 * integers 1, 10, 20, 30:
 *
 * ```
 * val result = flow.conflate().onEach { delay(1000) }.toList()
 * assertEquals(listOf(1, 10, 20, 30), result)
 * ```
 *
 * Note that `conflate` operator is a shortcut for [buffer] with `capacity` of [Channel.CONFLATED][Channel.CONFLATED],
 * which is, in turn, a shortcut to a buffer that only keeps the latest element as
 * created by `buffer(onBufferOverflow = `[`BufferOverflow.DROP_OLDEST`][BufferOverflow.DROP_OLDEST]`)`.
 *
 * ### Operator fusion
 *
 * Adjacent applications of `conflate`/[buffer], [channelFlow], [flowOn] and [produceIn] are
 * always fused so that only one properly configured channel is used for execution.
 * **Conflation takes precedence over `buffer()` calls with any other capacity.**
 *
 * Note that any instance of [StateFlow] already behaves as if `conflate` operator is
 * applied to it, so applying `conflate` to a `StateFlow` has no effect.
 * See [StateFlow] documentation on Operator Fusion.
 */
public fun <T> Flow<T>.conflate(): Flow<T> = buffer(CONFLATED)

/**
 * Changes the context where this flow is executed to the given [context].
 * This operator is composable and affects only preceding operators that do not have its own context.
 * This operator is context preserving: [context] **does not** leak into the downstream flow.
 *
 * For example:
 *
 * ```
 * withContext(Dispatchers.Main) {
 *     val singleValue = intFlow // will be executed on IO if context wasn't specified before
 *         .map { ... } // Will be executed in IO
 *         .flowOn(Dispatchers.IO)
 *         .filter { ... } // Will be executed in Default
 *         .flowOn(Dispatchers.Default)
 *         .single() // Will be executed in the Main
 * }
 * ```
 *
 * For more explanation of context preservation please refer to [Flow] documentation.
 *
 * This operator retains a _sequential_ nature of flow if changing the context does not call for changing
 * the [dispatcher][CoroutineDispatcher]. Otherwise, if changing dispatcher is required, it collects
 * flow emissions in one coroutine that is run using a specified [context] and emits them from another coroutines
 * with the original collector's context using a channel with a [default][Channel.BUFFERED] buffer size
 * between two coroutines similarly to [buffer] operator, unless [buffer] operator is explicitly called
 * before or after `flowOn`, which requests buffering behavior and specifies channel size.
 *
 * Note, that flows operating across different dispatchers might lose some in-flight elements when cancelled.
 * In particular, this operator ensures that downstream flow does not resume on cancellation even if the element
 * was already emitted by the upstream flow.
 *
 * ### Operator fusion
 *
 * Adjacent applications of [channelFlow], [flowOn], [buffer], and [produceIn] are
 * always fused so that only one properly configured channel is used for execution.
 *
 * Multiple `flowOn` operators fuse to a single `flowOn` with a combined context. The elements of the context of
 * the first `flowOn` operator naturally take precedence over the elements of the second `flowOn` operator
 * when they have the same context keys, for example:
 *
 * ```
 * flow.map { ... } // Will be executed in IO
 *     .flowOn(Dispatchers.IO) // This one takes precedence
 *     .flowOn(Dispatchers.Default)
 * ```
 *
 * Note that an instance of [SharedFlow] does not have an execution context by itself,
 * so applying `flowOn` to a `SharedFlow` has not effect. See the [SharedFlow] documentation on Operator Fusion.
 *
 * @throws [IllegalArgumentException] if provided context contains [Job] instance.
 */
public fun <T> Flow<T>.flowOn(context: CoroutineContext): Flow<T> {
    checkFlowContext(context)
    return when {
        context == EmptyCoroutineContext -> this
        this is FusibleFlow -> fuse(context = context)
        else -> ChannelFlowOperatorImpl(this, context = context)
    }
}

/**
 * Returns a flow which checks cancellation status on each emission and throws
 * the corresponding cancellation cause if flow collector was cancelled.
 * Note that [flow] builder and all implementations of [SharedFlow] are [cancellable] by default.
 *
 * This operator provides a shortcut for `.onEach { currentCoroutineContext().ensureActive() }`.
 * See [ensureActive][CoroutineContext.ensureActive] for details.
 */
public fun <T> Flow<T>.cancellable(): Flow<T> =
    when (this) {
        is CancellableFlow<*> -> this // Fast-path, already cancellable
        else -> CancellableFlowImpl(this)
    }

/**
 * Internal marker for flows that are [cancellable].
 */
internal interface CancellableFlow<out T> : Flow<T>

/**
 * Named implementation class for a flow that is defined by the [cancellable] function.
 */
private class CancellableFlowImpl<T>(private val flow: Flow<T>) : CancellableFlow<T> {
    override suspend fun collect(collector: FlowCollector<T>) {
        flow.collect {
            currentCoroutineContext().ensureActive()
            collector.emit(it)
        }
    }
}

private fun checkFlowContext(context: CoroutineContext) {
    require(context[Job] == null) {
        "Flow context cannot contain job in it. Had $context"
    }
}
