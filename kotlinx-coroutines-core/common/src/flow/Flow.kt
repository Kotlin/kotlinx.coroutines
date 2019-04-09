/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*

/**
 * A cold asynchronous stream of the data, that emits from zero to N (where N can be unbounded) values and completes normally or with an exception.
 *
 * All transformations on the flow, such as [map] and [filter] do not trigger flow collection or execution, only terminal operators (e.g. [single]) do trigger it.
 *
 * Flow can be collected in a suspending manner, without actual blocking, using [collect] extension that will complete normally or exceptionally:
 * ```
 * try {
 *     flow.collect { value ->
 *         println("Received $value")
 *     }
 * } catch (e: Exception) {
 *     println("Flow has thrown an exception: $e")
 * }
 * ```
 * Additionally, the library provides a rich set of terminal operators such as [single], [reduce] and others.
 *
 * Flow does not carry information whether it is a cold stream (that can be collected multiple times and
 * triggers its evaluation every time [collect] is executed) or a hot one, but conventionally flow represents a cold stream.
 * Transitions between hot and cold streams are supported via channels and the corresponding API: [flowViaChannel], [broadcastIn], [produceIn].
 *
 * Flow has a context preserving property: it encapsulates its own execution context and never propagates or leaks it to the downstream, thus making
 * reasoning about execution context of particular transformations or terminal operations trivial.
 *
 * There are two ways of changing the flow's context: [flowOn][Flow.flowOn] and [flowWith][Flow.flowWith].
 * The former changes the upstream context ("everything above the flowOn operator") while the latter
 * changes the context of the flow within [flowWith] body. For additional information refer to these operators documentation.
 *
 * This reasoning can be demonstrated in the practice:
 * ```
 * val flow = flowOf(1, 2, 3)
 *     .map { it + 1 } // Will be executed in ctx_1
 *     .flowOn(ctx_1) // Changes upstream context: flowOf and map
 *
 * // Now we have flow that is context-preserving: it is executed somewhere but this information is encapsulated in the flow itself
 *
 * val filtered = flow // ctx_1 is inaccessible
 *    .filter { it == 3 } // Pure operator without a context yet
 *
 * withContext(Dispatchers.Main) {
 *     // All not encapsulated operators will be executed in Main: filter and single
 *     val result = filtered.single()
 *     myUi.text = result
 * }
 * ```
 *
 * From the implementation point of view it means that all intermediate operators on [Flow] should use the following constraint:
 * If one wants to separate collection or emission into multiple coroutines, it should use [coroutineScope] or [supervisorScope] and
 * is not allowed to modify coroutines context:
 * ```
 * fun <T> Flow<T>.buffer(bufferSize: Int): Flow<T> = flow {
 *     coroutineScope { // coroutine scope is necessary, withContext is prohibited
 *         val channel = Channel<T>(bufferSize)
 *         // GlobalScope.launch { is prohibited
 *         // launch(Dispatchers.IO) { is prohibited
 *         launch { // is OK
 *             collect { value ->
 *                 channel.send(value)
 *             }
 *             channel.close()
 *         }
 *
 *         for (i in channel) {
 *             emit(i)
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
     *
     * Only coroutine builders that inherit the context are allowed, for example the following code is fine:
     * ```
     * coroutineScope { // Context is inherited
     *     launch { // Dispatcher is not overridden, fine as well
     *         collector.emit(someValue)
     *     }
     * }
     * ```
     *
     * 2) It should serialize calls to [emit][FlowCollector.emit] as [FlowCollector] implementations are not thread safe by default.
     */
    public suspend fun collect(collector: FlowCollector<in T>)
}
