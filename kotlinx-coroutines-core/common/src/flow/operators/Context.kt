/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
 * When operator's code takes time to execute this decreases the total execution time of the flow.
 * A [channel][Channel] is used between the coroutines to send elements emitted by the coroutine `P` to
 * the coroutine `Q`. If the code before `buffer` operator (in the coroutine `P`) is faster than the code after
 * `buffer` operator (in the coroutine `Q`), then this channel will become full at some point and will suspend
 * the producer coroutine `P` until the consumer coroutine `Q` catches up.
 * The [capacity] parameter defines the size of this buffer.
 *
 * ### Operator fusion
 *
 * Adjacent applications of [channelFlow], [flowOn], [buffer], [produceIn], and [broadcastIn] are
 * always fused so that only one properly configured channel is used for execution.
 *
 * Explicitly specified buffer capacity takes precedence over `buffer()` or `buffer(Channel.BUFFERED)` calls,
 * which effectively requests a buffer of any size. Multiple requests with a specified buffer
 * size produce a buffer with the sum of the requested buffer sizes.
 *
 * ### Conceptual implementation
 *
 * The actual implementation of `buffer` is not trivial due to the fusing, but conceptually its
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
 * Usage of this function with [capacity] of [Channel.CONFLATED][Channel.CONFLATED] is provided as a shortcut via
 * [conflate] operator. See its documentation for details.
 *
 * @param capacity type/capacity of the buffer between coroutines. Allowed values are the same as in `Channel(...)`
 * factory function: [BUFFERED][Channel.BUFFERED] (by default), [CONFLATED][Channel.CONFLATED],
 * [RENDEZVOUS][Channel.RENDEZVOUS], [UNLIMITED][Channel.UNLIMITED] or a non-negative value indicating
 * an explicitly requested size.
 */
@ExperimentalCoroutinesApi
public fun <T> Flow<T>.buffer(capacity: Int = BUFFERED): Flow<T> {
    require(capacity >= 0 || capacity == BUFFERED || capacity == CONFLATED) {
        "Buffer size should be non-negative, BUFFERED, or CONFLATED, but was $capacity"
    }
    return if (this is ChannelFlow)
        update(capacity = capacity)
    else
        ChannelFlowOperatorImpl(this, capacity = capacity)
}

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
 * Note that `conflate` operator is a shortcut for [buffer] with `capacity` of [Channel.CONFLATED][Channel.CONFLATED].
 *
 * ### Operator fusion
 *
 * Adjacent applications of `conflate`/[buffer], [channelFlow], [flowOn], [produceIn], and [broadcastIn] are
 * always fused so that only one properly configured channel is used for execution.
 * **Conflation takes precedence over `buffer()` calls with any other capacity.**
 */
@ExperimentalCoroutinesApi
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
 * This operators retains a _sequential_ nature of flow if changing the context does not call for changing
 * the [dispatcher][CoroutineDispatcher]. Otherwise, if changing dispatcher is required, it collects
 * flow emissions in one coroutine that is run using a specified [context] and emits them from another coroutines
 * with the original collector's context using a channel with a [default][Channel.BUFFERED] buffer size
 * between two coroutines similarly to [buffer] operator, unless [buffer] operator is explicitly called
 * before or after `flowOn`, which requests buffering behavior and specifies channel size.
 *
 * ### Operator fusion
 *
 * Adjacent applications of [channelFlow], [flowOn], [buffer], [produceIn], and [broadcastIn] are
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
 * @throws [IllegalArgumentException] if provided context contains [Job] instance.
 */
@ExperimentalCoroutinesApi
public fun <T> Flow<T>.flowOn(context: CoroutineContext): Flow<T> {
    checkFlowContext(context)
    return when {
        context == EmptyCoroutineContext -> this
        this is ChannelFlow -> update(context = context)
        else -> ChannelFlowOperatorImpl(this, context = context)
    }
}

/**
 * The operator that changes the context where all transformations applied to the given flow within a [builder] are executed.
 * This operator is context preserving and does not affect the context of the preceding and subsequent operations.
 *
 * Example:
 *
 * ```
 * flow // not affected
 *     .map { ... } // Not affected
 *     .flowWith(Dispatchers.IO) {
 *         map { ... } // in IO
 *         .filter { ... } // in IO
 *     }
 *     .map { ... } // Not affected
 * ```
 *
 * For more explanation of context preservation please refer to [Flow] documentation.
 *
 * This operator is deprecated without replacement because it was discovered that it doesn't play well with coroutines
 * and flow semantics:
 *
 * 1) It doesn't prevent context elements from the downstream to leak into its body
 *     ```
 *     flowOf(1).flowWith(EmptyCoroutineContext) {
 *         onEach { println(kotlin.coroutines.coroutineContext[CoroutineName]) } // Will print 42
 *     }.flowOn(CoroutineName(42))
 *     ```
 * 2) To avoid such leaks, new primitive should be introduced to `kotlinx.coroutines` -- the subtraction of contexts.
 *    And this will become a new concept to learn, maintain and explain.
 * 3) It defers the execution of declarative [builder] until the moment of [collection][Flow.collect] similarly
 *    to `Observable.defer`. But it is unexpected because nothing in the name `flowWith` reflects this fact.
 * 4) It can be confused with [flowOn] operator, though [flowWith] is much rarer.
 */
@FlowPreview
@Deprecated(message = "flowWith is deprecated without replacement, please refer to its KDoc for an explanation", level = DeprecationLevel.WARNING) // Error in beta release, removal in 1.4
public fun <T, R> Flow<T>.flowWith(
    flowContext: CoroutineContext,
    bufferSize: Int = BUFFERED,
    builder: Flow<T>.() -> Flow<R>
): Flow<R> {
    checkFlowContext(flowContext)
    val source = this
    return unsafeFlow {
        /**
         * Here we should remove a Job instance from the context.
         * All builders are written using scoping and no global coroutines are launched, so it is safe not to provide explicit Job.
         * It is also necessary not to mess with cancellation if multiple flowWith are used.
         */
        val originalContext = coroutineContext.minusKey(Job)
        val prepared = source.flowOn(originalContext).buffer(bufferSize)
        builder(prepared).flowOn(flowContext).buffer(bufferSize).collect { value ->
            return@collect emit(value)
        }
    }
}

private fun checkFlowContext(context: CoroutineContext) {
    require(context[Job] == null) {
        "Flow context cannot contain job in it. Had $context"
    }
}
