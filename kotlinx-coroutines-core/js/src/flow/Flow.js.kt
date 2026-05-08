@file:OptIn(ExperimentalJsExport::class, ExperimentalJsStatic::class, ExperimentalStdlibApi::class)
@file:Suppress("INVISIBLE_REFERENCE", "EXPOSED_FUNCTION_RETURN_TYPE", "EXPOSED_PARAMETER_TYPE")
package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.ClosedReceiveChannelException
import kotlinx.coroutines.channels.ClosedSendChannelException
import kotlin.js.Promise
import kotlin.js.JsSymbol

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
 * - [flowOf(...)][flowOf] functions to create a flow from a fixed set of values.
 * - [asFlow()][asFlow] extension functions on various types to convert them into flows.
 * - [flow { ... }][flow] builder function to construct arbitrary flows from
 *   sequential calls to [emit][FlowCollector.emit] function.
 * - [channelFlow { ... }][channelFlow] builder function to construct arbitrary flows from
 *   potentially concurrent calls to the [send][kotlinx.coroutines.channels.SendChannel.send] function.
 * - [MutableStateFlow] and [MutableSharedFlow] define the corresponding constructor functions to create
 *   a _hot_ flow that can be directly updated.
 *
 * ### Flow constraints
 *
 * All implementations of the `Flow` interface must adhere to two key properties described in detail below:
 *
 * - Context preservation.
 * - Exception transparency.
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
 * only emit from the same coroutine context.
 * This constraint is efficiently enforced by the default [flow] builder.
 * The [flow] builder should be used if the flow implementation does not start any coroutines.
 * Its implementation prevents most of the development mistakes:
 *
 * ```
 * val myFlow = flow {
 *     // GlobalScope.launch { // is prohibited
 *     // launch(Dispatchers.IO) { // is prohibited
 *     // withContext(CoroutineName("myFlow")) { // is prohibited
 *     emit(1) // OK
 *     coroutineScope {
 *         emit(2) // OK -- still the same coroutine
 *     }
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
 * - Scoped primitive should be used to provide a [CoroutineScope].
 * - Changing the context of emission is prohibited, no matter whether it is `withContext(ctx)` or
 *   a builder argument (e.g. `launch(ctx)`).
 * - Collecting another flow from a separate context is allowed, but it has the same effect as
 *   applying the [flowOn] operator to that flow, which is more efficient.
 *
 * ### Exception transparency
 *
 * When `emit` or `emitAll` throws, the Flow implementations must immediately stop emitting new values and finish with an exception.
 * For diagnostics or application-specific purposes, the exception may be different from the one thrown by the emit operation,
 * suppressing the original exception as discussed below.
 * If there is a need to emit values after the downstream failed, please use the [catch][Flow.catch] operator.
 *
 * The [catch][Flow.catch] operator only catches upstream exceptions, but passes
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
 * All exception-handling Flow operators follow the principle of exception suppression:
 *
 * If the upstream flow throws an exception during its completion when the downstream exception has been thrown,
 * the downstream exception becomes superseded and suppressed by the upstream exception, being a semantic
 * equivalent of throwing from `finally` block. However, this doesn't affect the operation of the exception-handling operators,
 * which consider the downstream exception to be the root cause and behave as if the upstream didn't throw anything.
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
 *
 * Use the `flow { ... }` builder function to create an implementation, or extend [AbstractFlow].
 * These implementations ensure that the context preservation property is not violated, and prevent most
 * of the developer mistakes related to concurrency, inconsistent flow dispatchers, and cancellation.
 */
@Suppress("INVISIBLE_REFERENCE", "EXPOSED_SUPER_INTERFACE")
@JsImplicitExport(true)
public actual interface Flow<out T> {

    /**
     * Accepts the given [collector] and [emits][FlowCollector.emit] values into it.
     *
     * This method can be used along with SAM-conversion of [FlowCollector]:
     * ```
     * myFlow.collect { value -> println("Collected $value") }
     * ```
     *
     * ### Method inheritance
     *
     * To ensure the context preservation property, it is not recommended implementing this method directly.
     * Instead, [AbstractFlow] can be used as the base type to properly ensure flow's properties.
     *
     * All default flow implementations ensure context preservation and exception transparency properties on a best-effort basis
     * and throw [IllegalStateException] if a violation was detected.
     */
    @JsExport.Ignore
    public actual suspend fun collect(collector: FlowCollector<T>)

    @JsSymbol("asyncIterator")
    public fun asyncIterator(): JsAsyncIterator<T> {
        val flow = this
        val demand = Channel<Unit>(Channel.RENDEZVOUS)
        val valueChannel = Channel<T>(Channel.RENDEZVOUS)

        val scope = CoroutineScope(SupervisorJob() + Dispatchers.Default)

        val producer = scope.launch(Dispatchers.Default) {
            try {
                flow.collect { value ->
                    demand.receive()
                    valueChannel.send(value)
                }
            } catch (e: CancellationException) {
                valueChannel.close()
                demand.close()
                throw e
            }
            catch (e: Throwable) {
                valueChannel.close(e)
                demand.close(e)
                return@launch
            }
            valueChannel.close()
            demand.close()
        }

        val asyncIteratorConstructor = js("typeof AsyncIterator === 'function' ? AsyncIterator : Object")
        val asyncIterator = js("Object.create(asyncIteratorConstructor.prototype)")

        asyncIterator.next = {
            scope.promise {
                val doneValue = js("({ value: undefined, done: true })")
                try {
                    // Signal demand for the next value
                    demand.send(Unit)
                    // Wait for the value
                    val result = valueChannel.receiveCatching()
                    if (result.isSuccess) {
                        val v = result.getOrNull()
                        js("({ value: v, done: false })")
                    } else {
                        result.exceptionOrNull()?.let { throw it }
                        doneValue
                    }
                } catch (e: ClosedReceiveChannelException) {
                    e.cause?.let { throw it }
                    doneValue
                } catch (e: ClosedSendChannelException) {
                    e.cause?.let { throw it }
                    doneValue
                }
            }
        }

        asyncIterator.`return` = {
            scope.promise {
                try {
                    if (!producer.isCancelled && producer.isActive) {
                        producer.cancel(CancellationException("Iterator returned early"))
                    }
                    js("({ value: undefined, done: true })")
                } finally {
                    demand.close()
                    valueChannel.close()
                }
            }
        }

        asyncIterator.`throw` = { err: Any? ->
            if (!producer.isCancelled && producer.isActive) {
                val message = "Iterator.throw was called"
                val cause = (err as? Throwable)
                    ?.let { CancellationException(message, it) } ?: CancellationException(message)

                producer.cancel(cause)
            }

            demand.close()
            valueChannel.close()
            js("Promise.reject(err)")
        }

        return asyncIterator
    }

    @JsExport.Ignore
    public companion object {
        /**
         * Converts a JavaScript AsyncIterable to a Kotlin Flow.
         *
         * The resulting flow will iterate through all values produced by the async iterable.
         * If the flow collection is canceled or fails, the iterator's `return()` method will be called
         * to properly clean up the async iterable.
         */
        @JsStatic
        public fun <T> from(async: JsAsyncIterable<T>): Flow<T> =
            from(async.asyncIterator())

        /**
         * Converts a JavaScript async generator function to a Kotlin Flow.
         *
         * The generator will be invoked to get an async iterator for collection.
         * Cancellation or failure during a collection triggers the iterator's `return()` method
         * to ensure proper cleanup.
         */
        @JsStatic
        @JsName("fromAsyncGenerator")
        public fun <T> from(generator: () -> JsAsyncIterator<T>): Flow<T> = flow {
            var completed = false
            val iterator = generator()
            try {
                while (true) {
                    val result = iterator.next().await()
                    if (result.done) {
                        completed = true
                        break
                    }
                    emit(result.value)
                }
            } finally {
                if (!completed) {
                        iterator.`return`().await()
                }
            }
        }

        /**
         * Converts a JavaScript AsyncIterator to a Kotlin Flow.
         *
         * The resulting flow emits items produced by the iterator until it reports completion.
         * If a collection is canceled or fails, the iterator's `return()` method is called
         * to close the iterator.
         */
        @JsStatic
        @JsName("fromAsyncIterator")
        public fun <T> from(iterator: JsAsyncIterator<T>): Flow<T> =
            from { iterator }
    }
}



@JsName("AsyncIterable")
internal external interface JsAsyncIterable<out T> {
    @JsSymbol("asyncIterator")
    public fun asyncIterator(): JsAsyncIterator<T>
}

@JsName("AsyncIterator")
internal external interface JsAsyncIterator<out T> {
    public fun next(): Promise<JsIteratorResult<T>>
    public fun `return`(value: @UnsafeVariance T = definedExternally): Promise<JsIteratorResult<T>>
    public fun `throw`(value: Any? = definedExternally): Promise<JsIteratorResult<T>>
}

@JsName("IteratorResult")
internal external interface JsIteratorResult<out T> {
    public val value: T
    public val done: Boolean
}
