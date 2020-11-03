/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlin.coroutines.*

/**
 * An asynchronous data stream that sequentially emits values and completes normally or with an exception.
 *
 * _Intermediate operators_ on the flow such as [map], [filter], [take], [zip], etc are functions that are
 * applied to the _upstream_ flow or flows and return a _downstream_ flow where further operators can be applied to.
 * Intermediate operations do not execute any code in the flow and are not suspending functions themselves.
 * They only set up a chain of operations for future execution and quickly return.
 * This is known as a _cold flow_ property.
 *
 * _Terminal operators_ on the flow are either suspending functions such as [collect], [single], [reduce], [toList], etc.
 * or [launchIn] operator that starts collection of the flow in the given scope.
 * They are applied to the upstream flow and trigger execution of all operations.
 * Execution of the flow is also called _collecting the flow_  and is always performed in a suspending manner
 * without actual blocking. Terminal operators complete normally or exceptionally depending on successful or failed
 * execution of all the flow operations in the upstream. The most basic terminal operator is [collect], for example:
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
 * By default, flows are _sequential_ and all flow operations are executed sequentially in the same coroutine,
 * with an exception for a few operations specifically designed to introduce concurrency into flow
 * execution such as [buffer] and [flatMapMerge]. See their documentation for details.
 *
 * The `Flow` interface does not carry information whether a flow is a _cold_ stream that can be collected repeatedly and
 * triggers execution of the same code every time it is collected, or if it is a _hot_ stream that emits different
 * values from the same running source on each collection. Usually flows represent _cold_ streams, but
 * there is a [SharedFlow] subtype that represents _hot_ streams. In addition to that, any flow can be turned
 * into a _hot_ one by the [stateIn] and [shareIn] operators, or by converting the flow into a hot channel
 * via the [produceIn] operator.
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
 *   potentially concurrent calls to the [send][kotlinx.coroutines.channels.SendChannel.send] function.
 * * [MutableStateFlow] and [MutableSharedFlow] define the corresponding constructor functions to create
 *   a _hot_ flow that can be directly updated.
 *
 * ### Flow constraints
 *
 * All implementations of the `Flow` interface must adhere to two key properties described in detail below:
 *
 * * Context preservation.
 * * Exception transparency.
 *
 * These properties ensure the ability to perform local reasoning about the code with flows and modularize the code
 * in such a way that upstream flow emitters can be developed separately from downstream flow collectors.
 * A user of a flow does not need to be aware of implementation details of the upstream flows it uses.
 *
 * ### Context preservation
 *
 * The flow has a context preservation property: it encapsulates its own execution context and never propagates or leaks
 * it downstream, thus making reasoning about the execution context of particular transformations or terminal
 * operations trivial.
 *
 * There is only one way to change the context of a flow: the [flowOn][Flow.flowOn] operator
 * that changes the upstream context ("everything above the `flowOn` operator").
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
 * From the implementation point of view, it means that all flow implementations should
 * only emit from the same coroutine.
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
 * Use [channelFlow] if the collection and emission of a flow are to be separated into multiple coroutines.
 * It encapsulates all the context preservation work and allows you to focus on your
 * domain-specific problem, rather than invariant implementation details.
 * It is possible to use any combination of coroutine builders from within [channelFlow].
 *
 * If you are looking for performance and are sure that no concurrent emits and context jumps will happen,
 * the [flow] builder can be used alongside a [coroutineScope] or [supervisorScope] instead:
 *  - Scoped primitive should be used to provide a [CoroutineScope].
 *  - Changing the context of emission is prohibited, no matter whether it is `withContext(ctx)` or
 *    a builder argument (e.g. `launch(ctx)`).
 *  - Collecting another flow from a separate context is allowed, but it has the same effect as
 *    applying the [flowOn] operator to that flow, which is more efficient.
 *
 * ### Exception transparency
 *
 * Flow implementations never catch or handle exceptions that occur in downstream flows. From the implementation standpoint
 * it means that calls to [emit][FlowCollector.emit] and [emitAll] shall never be wrapped into
 * `try { ... } catch { ... }` blocks. Exception handling in flows shall be performed with
 * [catch][Flow.catch] operator and it is designed to only catch exceptions coming from upstream flows while passing
 * all downstream exceptions. Similarly, terminal operators like [collect][Flow.collect]
 * throw any unhandled exceptions that occur in their code or in upstream flows, for example:
 *
 * ```
 * flow { emitData() }
 *     .map { computeOne(it) }
 *     .catch { ... } // catches exceptions in emitData and computeOne
 *     .map { computeTwo(it) }
 *     .collect { process(it) } // throws exceptions from process and computeTwo
 * ```
 * The same reasoning can be applied to the [onCompletion] operator that is a declarative replacement for the `finally` block.
 *
 * Failure to adhere to the exception transparency requirement can lead to strange behaviors which make
 * it hard to reason about the code because an exception in the `collect { ... }` could be somehow "caught"
 * by an upstream flow, limiting the ability of local reasoning about the code.
 *
 * Flow machinery enforces exception transparency at runtime and throws [IllegalStateException] on any attempt to emit a value,
 * if an exception has been thrown on previous attempt.
 *
 * ### Reactive streams
 *
 * Flow is [Reactive Streams](http://www.reactive-streams.org/) compliant, you can safely interop it with
 * reactive streams using [Flow.asPublisher] and [Publisher.asFlow] from `kotlinx-coroutines-reactive` module.
 *
 * ### Not stable for inheritance
 *
 * **The `Flow` interface is not stable for inheritance in 3rd party libraries**, as new methods
 * might be added to this interface in the future, but is stable for use.
 * Use the `flow { ... }` builder function to create an implementation.
 */
public interface Flow<out T> {
    /**
     * Accepts the given [collector] and [emits][FlowCollector.emit] values into it.
     * This method should never be implemented or used directly.
     *
     * The only way to implement the `Flow` interface directly is to extend [AbstractFlow].
     * To collect it into a specific collector, either `collector.emitAll(flow)` or `collect { ... }` extension
     * should be used. Such limitation ensures that the context preservation property is not violated and prevents most
     * of the developer mistakes related to concurrency, inconsistent flow dispatchers and cancellation.
     */
    @InternalCoroutinesApi
    public suspend fun collect(collector: FlowCollector<T>)
}

/**
 * Base class for stateful implementations of `Flow`.
 * It tracks all the properties required for context preservation and throws an [IllegalStateException]
 * if any of the properties are violated.
 * 
 * Example of the implementation:
 *
 * ```
 * // list.asFlow() + collect counter
 * class CountingListFlow(private val values: List<Int>) : AbstractFlow<Int>() {
 *     private val collectedCounter = AtomicInteger(0)
 *
 *     override suspend fun collectSafely(collector: FlowCollector<Int>) {
 *         collectedCounter.incrementAndGet() // Increment collected counter
 *         values.forEach { // Emit all the values
 *             collector.emit(it)
 *         }
 *     }
 *
 *     fun toDiagnosticString(): String = "Flow with values $values was collected ${collectedCounter.value} times"
 * }
 * ```
 */
@FlowPreview
public abstract class AbstractFlow<T> : Flow<T>, CancellableFlow<T> {

    @InternalCoroutinesApi
    public final override suspend fun collect(collector: FlowCollector<T>) {
        val safeCollector = SafeCollector(collector, coroutineContext)
        try {
            collectSafely(safeCollector)
        } finally {
            safeCollector.releaseIntercepted()
        }
    }

    /**
     * Accepts the given [collector] and [emits][FlowCollector.emit] values into it.
     *
     * A valid implementation of this method has the following constraints:
     * 1) It should not change the coroutine context (e.g. with `withContext(Dispatchers.IO)`) when emitting values.
     *    The emission should happen in the context of the [collect] call.
     *    Please refer to the top-level [Flow] documentation for more details.
     * 2) It should serialize calls to [emit][FlowCollector.emit] as [FlowCollector] implementations are not
     *    thread-safe by default.
     *    To automatically serialize emissions [channelFlow] builder can be used instead of [flow]
     *
     * @throws IllegalStateException if any of the invariants are violated.
     */
    public abstract suspend fun collectSafely(collector: FlowCollector<T>)
}
