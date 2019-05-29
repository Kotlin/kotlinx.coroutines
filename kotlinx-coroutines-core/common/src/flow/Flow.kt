/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*

/**
 * A cold asynchronous data stream that sequentially emits values
 * and completes normally or with an exception.
 *
 * _Cold flow_ means that intermediate operators on a flow such as [map] and [filter] do not trigger its execution,
 * which is only done by terminal operators like [single]. By default, flows are _sequential_ and all flow
 * operations are executed sequentially in the same coroutine, see [buffer] for details.
 *
 * _Collecting the flow_ means executing all its operations.
 * Flow values can be collected in a suspending manner without actual blocking using the [collect] extension that
 * completes normally or exceptionally:
 *
 * ```
 * try {
 *     flow.collect { value ->
 *         println("Received $value")
 *     }
 * } catch (e: Exception) {
 *     println("The flow has thrown an exception: $e")
 * }
 * ```
 *
 * Additionally, the library provides a rich set of terminal operators such as [single], [reduce] and others.
 *
 * Flows don't carry information whether they are cold streams (which can be collected repeatedly and
 * trigger their evaluation every time [collect] is executed) or hot ones, but, conventionally, they represent cold streams.
 * Transitions between hot and cold streams are supported via channels and the corresponding API:
 * [channelFlow], [produceIn], [broadcastIn].
 *
 * ### Flow builders
 *
 * There are the following basic ways to create a flow:
 *
 * * [flowOf(...)][flowOf] functions to create a flow from a fixed set of values.
 * * [asFlow()][asFlow] extension functions on various types to convert them into flows.
 * * [flow { ... }][flow] builder function to construct arbitrary flows from
 *   sequential calls to [emit][FlowCollector.emit] function.
 * * [channelFlow { ... }][channelFlow] builder function to construct arbitrary flows from
 *   potentially concurrent calls to [send][kotlinx.coroutines.channels.SendChannel.send] function.
 *
 * ### Flow context
 *
 * The flow has a context preservation property: it encapsulates its own execution context and never propagates or leaks
 * it downstream, thus making reasoning about the execution context of particular transformations or terminal
 * operations trivial.
 *
 * There is the only way to change the context of a flow: [flowOn][Flow.flowOn] operator,
 * that changes the upstream context ("everything above the flowOn operator").
 * For additional information refer to its documentation.
 *
 * This reasoning can be demonstrated in practice:
 *
 * ```
 * val flowA = flowOf(1, 2, 3)
 *     .map { it + 1 } // Will be executed in ctxA
 *     .flowOn(ctxA) // Changes the upstream context: flowOf and map
 *
 * // Now we have a context-preserving flow: it is executed somewhere but this information is encapsulated in the flow itself
 *
 * val filtered = flowA // ctxA is encapsulated in flowA
 *    .filter { it == 3 } // Pure operator without a context yet
 *
 * withContext(Dispatchers.Main) {
 *     // All non-encapsulated operators will be executed in Main: filter and single
 *     val result = filtered.single()
 *     myUi.text = result
 * }
 * ```
 *
 * From the implementation point of view it means that all flow implementations should
 * emit only from the same coroutine.
 * This constraint is efficiently enforced by the default [flow] builder.
 * The [flow] builder should be used if flow implementation does not start any coroutines.
 * Its implementation prevents most of the development mistakes:
 *
 * ```
 * val myFlow = flow {
 *    // GlobalScope.launch { // is prohibited
 *    // launch(Dispatchers.IO) { // is prohibited
 *    // withContext(CoroutineName("myFlow")) // is prohibited
 *    emit(1) // OK
 *    coroutineScope {
 *        emit(2) // OK -- still the same coroutine
 *    }
 * }
 * ```
 *
 * Use [channelFlow] if the collection and emission of the flow are to be separated into multiple coroutines.
 * It encapsulates all the context preservation work and allows you to focus on your
 * domain-specific problem, rather than invariant implementation details.
 * It is possible to use any combination of coroutine builders from within [channelFlow].
 *
 * If you are looking for the performance and are sure that no concurrent emits and context jumps will happen,
 * [flow] builder alongside with [coroutineScope] or [supervisorScope] can be used instead:
 *  - Scoped primitive should be used to provide a [CoroutineScope].
 *  - Changing the context of emission is prohibited, no matter whether it is `withContext(ctx)` or
 *    builder argument (e.g. `launch(ctx)`).
 *  - Collecting another flow from a separate context is allowed, but it has the same effect as
 *    [flowOn] operator on that flow, which is more efficient.
 *
 * Flow is [Reactive Streams](http://www.reactive-streams.org/) compliant, you can safely interop it with
 * reactive streams using [Flow.asPublisher] and [Publisher.asFlow] from kotlinx-coroutines-reactive module.
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
     * 2) It should serialize calls to [emit][FlowCollector.emit] as [FlowCollector] implementations are not
     * thread safe by default.
     *    To automatically serialize emissions [channelFlow] builder can be used instead of [flow]
     */
    public suspend fun collect(collector: FlowCollector<T>)
}
