/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*

/**
 * A cold asynchronous data stream emitting zero to N (where N can be unbounded) values and completing normally or with an exception.
 *
 * Transformations on a flow, such as [map] and [filter], do not trigger its collection or execution (which is only done by terminal operators like [single]).
 *
 * A flow can be collected in a suspending manner, without actual blocking, using the [collect] extension that will complete normally or exceptionally:
 * ```
 * try {
 *     flow.collect { value ->
 *         println("Received $value")
 *     }
 * } catch (e: Exception) {
 *     println("The flow has thrown an exception: $e")
 * }
 * ```
 * Additionally, the library provides a rich set of terminal operators such as [single], [reduce] and others.
 *
 * Flows don't carry information whether they are cold streams (which can be collected repeatedly and
 * trigger their evaluation every time [collect] is executed) or hot ones, but, conventionally, they represent cold streams.
 * Transitions between hot and cold streams are supported via channels and the corresponding API: [flowViaChannel], [broadcastIn], [produceIn].
 *
 * The flow has a context preservation property: it encapsulates its own execution context and never propagates or leaks it downstream, thus making
 * reasoning about the execution context of particular transformations or terminal operations trivial.
 *
 * There are two ways to change the context of a flow: [flowOn][Flow.flowOn] and [flowWith][Flow.flowWith].
 * The former changes the upstream context ("everything above the flowOn operator") while the latter
 * changes the context of the flow within [flowWith] body. For additional information refer to these operators' documentation.
 *
 * This reasoning can be demonstrated in practice:
 * ```
 * val flow = flowOf(1, 2, 3)
 *     .map { it + 1 } // Will be executed in ctx_1
 *     .flowOn(ctx_1) // Changes the upstream context: flowOf and map
 *
 * // Now we have a context-preserving flow: it is executed somewhere but this information is encapsulated in the flow itself
 *
 * val filtered = flow // ctx_1 is inaccessible
 *    .filter { it == 3 } // Pure operator without a context yet
 *
 * withContext(Dispatchers.Main) {
 *     // All non-encapsulated operators will be executed in Main: filter and single
 *     val result = filtered.single()
 *     myUi.text = result
 * }
 * ```
 *
 * From the implementation point of view it means that all intermediate operators on [Flow] should abide by the following constraints:
 * 1) If an operator is trivial and does not start any coroutines, regular [flow] builder should be used. Its implementation
 *    efficiently enforces all the invariants and prevents most of the development mistakes.
 *
 * 2) If the collection and emission of the flow are to be separated into multiple coroutines, [channelFlow] should be used.
 *   [channelFlow] encapsulates all the context preservation work and allows you to focus on your domain-specific problem,
 *   rather than invariant implementation details.  It is possible to use any combination of coroutine builders from within [channelFlow].
 *
 * 3) If you are looking for the performance and are sure that no concurrent emits and context jumps will happen, [flow] builder
 *    alongside with [coroutineScope] or [supervisorScope] can be used instead:
 *
 *    - Scoped primitive should be used to provide a [CoroutineScope]
 *    - Changing the context of emission is prohibited, no matter whether it is `withContext(ctx)` or builder argument (e.g. `launch(ctx)`)
 *    - Changing the context of collection is allowed, but it has the same effect as [flowOn] operator and changes the upstream context.
 *
 * These constraints are enforced by the default [flow] builder.
 * Example of the proper `buffer` implementation:
 * ```
 * fun <T> Flow<T>.buffer(bufferSize: Int): Flow<T> = flow {
 *     coroutineScope { // coroutine scope is necessary, withContext is prohibited
 *         // GlobalScope.produce { is prohibited
 *         val channel = produce(bufferSize) {
 *             collect { value -> // Collect from started coroutine -- OK
 *                 channel.send(value)
 *             }
 *         }
 *
 *         for (i in channel) {
 *             emit(i) // Emission from the enclosing scope -- OK
 *             // launch { emit(i) } -- prohibited
 *             // withContext(Dispatchers.IO) { emit(i) }
 *         }
 *     }
 * }
 * ```
 *
 * Flow is [Reactive Streams](http://www.reactive-streams.org/) compliant, you can safely interop it with reactive streams using [Flow.asPublisher] and [Publisher.asFlow] from
 * kotlinx-coroutines-reactive module.
 */
@FlowPreview
public interface Flow<out T> {

    /**
     * Accepts the given [collector] and [emits][FlowCollector.emit] values into it.
     *
     * A valid implementation of this method has the following constraints:
     * 1) It should not change the coroutine context (e.g. with `withContext(Dispatchers.IO)`) when emitting values.
     *    The emission should happen in the context of the [collect] call.
     *    Please refer to the top-level [Flow] documentation for more details.
     *
     * 2) It should serialize calls to [emit][FlowCollector.emit] as [FlowCollector] implementations are not thread safe by default.
     *    To automatically serialize emissions [channelFlow] builder can be used instead of [flow]
     */
    public suspend fun collect(collector: FlowCollector<T>)
}
