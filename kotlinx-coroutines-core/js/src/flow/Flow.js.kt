@file:OptIn(ExperimentalJsStatic::class, ExperimentalWasmJsInterop::class, ExperimentalStdlibApi::class)
package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.coroutines.CoroutineContext
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlin.js.*

@Suppress("INVISIBLE_REFERENCE") @JsOptionalExport(couldBeConvertedToExplicitExport = true)
public actual interface Flow<out T> {
    @JsExport.Ignore
    public actual suspend fun collect(collector: FlowCollector<T>)

    /**
     * Returns a JavaScript [`AsyncIterator`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/AsyncIterator)
     * for this [Flow].
     *
     * This method is used to implement the JavaScript [async-iteration protocol](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Iteration_protocols#the_async_iterator_and_async_iterable_protocols),
     * to support [collecting][Flow.collect] this [Flow] with `for await ... of`.
     *
     * The JavaScript side does not propagate any [CoroutineContext] to the [Flow.collect] call. Therefore:
     * - The coroutine context of the new coroutine is [Dispatchers.Default]; nothing is inherited from the caller.
     *   To configure the coroutine context of the flow, use [flowOn].
     * - The collection has no parent [Job]: it is not cancelled together with any Kotlin scope,
     *   and its lifecycle is controlled solely through the iterator (`next`, `return`, `throw`).
     *
     * The flow is collected lazily: the collection starts on the first `next()` call, and subsequent elements
     * are relayed with rendezvous-style backpressure consistently with the behavior of asynchronous iterators.
     * Each `next()` call synchronously runs the flow until the next element is emitted (or until the flow suspends),
     * and the flow stays suspended at `emit` until the next element is requested. Nothing is buffered.
     * Use [buffer] to configure this behavior and remove or reduce the backpressure.
     *
     * Early exit via `return` or `throw` cancels the collection and settles the returned promise only after
     * the flow has finished its cleanup. Like in async generators, calls are queued: `return`/`throw` take effect
     * only after the previously issued `next()` calls are settled. `throw(error)` aborts the collection by throwing
     * `error` from the suspended `emit` if it is a [Throwable] (otherwise it acts like `return()`).
     * If the flow fails, the pending `next()` promise is rejected with the exception, and the following calls
     * report completion.
     *
     * JavaScript/TypeScript usage:
     * ```javascript
     * for await (const value of flow) {
     *     console.log(value)
     * }
     *```
     *
     * This API is experimental: behavior and lifecycle semantics may change in future releases.
     */
    @JsSymbol("asyncIterator")
    // the deprecation message must be empty, or the API will be exported as deprecated to JS
    @Deprecated("", level = DeprecationLevel.HIDDEN)
    @Suppress("EXPOSED_FUNCTION_RETURN_TYPE")
    public fun asyncIterator(): JsAsyncIterableIterator<T> {
        fun resolveRequestWithoutElement(request: FlowAsyncIteratorResolution<T>) {
            when (request.command) {
                FlowAsyncIteratorCommand.NEXT_ELEMENT ->
                    request.resolve(JsIteratorResult(done = true))
                FlowAsyncIteratorCommand.MUST_RETURN ->
                    request.resolve(JsIteratorResult(value = request.valueToReturn, done = true))
                FlowAsyncIteratorCommand.MUST_THROW -> request.reject(request.valueToThrow)
            }
        }
        val elementRequests = Channel(onUndeliveredElement = ::resolveRequestWithoutElement)
        fun scheduleNextCommand(
            command: FlowAsyncIteratorCommand.CommandType, value: Any?
        ) = Promise { resolve, reject ->
            val ourRequest = FlowAsyncIteratorResolution(resolve, reject, command, value)
            GlobalScope.launch(start = CoroutineStart.UNDISPATCHED) {
                try {
                    elementRequests.send(ourRequest)
                } catch (_: ClosedSendChannelException) {
                    resolveRequestWithoutElement(ourRequest)
                }
            }
        }
        GlobalScope.launch(Dispatchers.Unconfined, start = CoroutineStart.UNDISPATCHED) {
            /** Receive the initial request. Until we know that some element is requested, we won't start the flow. */
            var currentRequest = elementRequests.receive()
            when (currentRequest.command) {
                FlowAsyncIteratorCommand.MUST_RETURN ->
                    currentRequest.resolve(JsIteratorResult(value = currentRequest.valueToReturn, done = true))
                FlowAsyncIteratorCommand.MUST_THROW -> currentRequest.reject(currentRequest.valueToThrow)
                FlowAsyncIteratorCommand.NEXT_ELEMENT -> {
                    try {
                        /* Collecting flow values until we receive a request to stop. */
                        collectWhile { element ->
                            currentRequest.resolve(JsIteratorResult(value = element, done = false))
                            currentRequest = withContext(NonCancellable) {
                                /** Using [NonCancellable] to ignore asynchronous upstream cancellation.
                                 * We are not allowed to make any progress until the next command arrives from JS,
                                 * so even when the upstream is making progress, we refuse to acknowledge it. */
                                elementRequests.receive()
                            }
                            when (currentRequest.command) {
                                FlowAsyncIteratorCommand.MUST_THROW -> {
                                    /** Let cancellation handlers know the exact exception that went through.
                                     * If there is no exception, we pretend this is a normal cancellation.
                                     * Consistency with JS doesn't force us to do anything specific,
                                     * as JS will throw `undefined` here, but we can't do that.
                                     */
                                    currentRequest.valueToThrow.toThrowableOrNull()?.let { throw it }
                                    false
                                }
                                FlowAsyncIteratorCommand.MUST_RETURN -> false
                                FlowAsyncIteratorCommand.NEXT_ELEMENT -> true
                                /* Should never happen */
                                else -> error(
                                    "Unexpected command value ${currentRequest.command}. " +
                                    "It should be either ${FlowAsyncIteratorCommand.MUST_THROW}, " +
                                    "${FlowAsyncIteratorCommand.MUST_RETURN}, or " +
                                    "${FlowAsyncIteratorCommand.NEXT_ELEMENT}"
                                )
                            }
                        }
                        resolveRequestWithoutElement(currentRequest)
                    } catch (e: dynamic) {
                        currentRequest.reject(e)
                    }
                }
            }
            elementRequests.cancel()
        }
        val iterator = JsAsyncIterator(
            next = { scheduleNextCommand(FlowAsyncIteratorCommand.NEXT_ELEMENT, js("undefined")) },
            _return = { scheduleNextCommand(FlowAsyncIteratorCommand.MUST_RETURN, it) },
            _throw = { scheduleNextCommand(FlowAsyncIteratorCommand.MUST_THROW, it) }
        )
        iterator.asDynamic()[js("Symbol.asyncIterator")] = { iterator }
        return iterator.unsafeCast<JsAsyncIterableIterator<T>>()
    }

    @JsExport.Ignore
    // Important note: it would be much nicer to place those factory functions outside of Flow
    // so from both Kotlin and TypeScript side it could be used without importing Flow (like in `flowOf` or `flow`)
    // However, the described way of exporting factory functions forces the functions always to be exported
    // (even if people don't use them and don't export Flow),
    // and that may cause bundle size problems (at least right now).
    // So, until the bundle size problem is solved, we keep those factory functions inside Flow, with possibility to move them outside later.
    @Suppress("JS_NAME_CLASH")
    // The name class allows to define overloads on the TypeScript side. Since we delegate to a single function,
    // shadowing on the JS side doesn't break implementation
    public companion object {
        /**
         * Represents a function returning a JS async iterator as a Kotlin Flow.
         *
         * The [items] will be invoked to get an async iterator separately for each [collect][Flow.collect] invocation.
         * `next()` is repeatedly called on the iterator until completion,
         * and the returned values are [emitted][FlowCollector.emit] downstream.
         *
         * If the downstream throws an exception, the collecting coroutine is cancelled or a `next()` call fails,
         * flow collection finishes prematurely.
         * In that case, `return()` is called on the iterator.
         * The completion of the [Promise] returned by `return()` is awaited in a non-cancellable manner.
         *
         * Usage example for JS:
         *
         * ```
         * Flow.fromAsync(async function* () { ... })
         * ```
         *
         * This API is experimental: behavior and lifecycle semantics may change in future releases.
         */
        @JsStatic
        @JsName("fromAsync")
        @Deprecated("", level = DeprecationLevel.HIDDEN)
        @Suppress("EXPOSED_PARAMETER_TYPE")
        public fun <T> fromAsync(items: () -> JsAsyncIterator<T>): Flow<T> =
            createFlowFromAsyncSource(items)

        /**
         * Represents a function returning a `JsAsyncIterable` as a Kotlin Flow.
         *
         * The [items] will be invoked to get an async iterator separately for each [collect][Flow.collect] invocation.
         * `next()` is repeatedly called on the iterator until completion,
         * and the returned values are [emitted][FlowCollector.emit] downstream.
         *
         * If the downstream throws an exception, the collecting coroutine is cancelled or a `next()` call fails,
         * flow collection finishes prematurely.
         * In that case, `return()` is called on the iterator.
         * The completion of the [Promise] returned by `return()` is awaited in a non-cancellable manner.
         *
         * Usage example for JS:
         *
         * ```
         * Flow.fromAsync(async function* () { ... })
         * ```
         *
         * This API is experimental: behavior and lifecycle semantics may change in future releases.
         */
        @JsStatic
        @JsName("fromAsync")
        @Deprecated("", level = DeprecationLevel.HIDDEN)
        @Suppress("EXPOSED_PARAMETER_TYPE")
        public fun <T> fromAsync(items: JsAsyncIterable<T>): Flow<T> =
            createFlowFromAsyncSource(items)
    }
}

private fun <T> createFlowFromAsyncSource(asyncSource: dynamic): Flow<T> {
    val asyncIteratorSymbol = js("Symbol.asyncIterator")
    val generator: () -> JsAsyncIterator<T> = when {
        jsTypeOf(asyncSource) == "function" -> asyncSource
        jsTypeOf(asyncSource[asyncIteratorSymbol]) == "function" -> {{ asyncSource[asyncIteratorSymbol]() }}
        else -> error("Expected a JS async iterable or a function returning an iterator, got $asyncSource")
    }
    return flow {
        val iterator = generator()
        while (true) {
            try {
                val result = iterator.next().await()
                if (result.done) break
                emit(result.value.unsafeCast<T>())
            } catch (e: dynamic) {
                // `return` function is optional in iterator
                // however we should always call it in case of an exception
                // to close the iterator.
                if (jsTypeOf(iterator.`return`) == "function") {
                    // We do this to not lose the exception thrown by `emit`/`next`
                    try {
                        // Prevent coroutine cancellation from making us exit before the cleanup is done
                        withContext(NonCancellable) {
                            iterator.`return`().await()
                        }
                    } catch (returnException: dynamic) {
                        if (e is CancellationException) throw returnException
                        (e as? Throwable)?.addSuppressed(returnException)
                    }
                }
                throw e
            }
        }
    }
}

private val <T> FlowAsyncIteratorResolution<T>.valueToReturn: T
    inline get() = value.unsafeCast<T>()

private val FlowAsyncIteratorResolution<*>.valueToThrow: JsPromiseError
    inline get() = value.unsafeCast<JsPromiseError>()

private external interface FlowAsyncIteratorResolution<T> {
    val resolve: (JsIteratorResult<T>) -> Unit
    val reject: (JsPromiseError) -> Unit

    /**
     * The kind of request issued by the JavaScript side of the async iterator protocol.
     *
     * Determines what the collection loop should do next and how [value] must be interpreted.
     * One of exactly three values:
     * - [FlowAsyncIteratorCommand.NEXT_ELEMENT] (`0`) —
     *   `next()` was called: run the flow until the next element is emitted.
     * - [FlowAsyncIteratorCommand.MUST_THROW] (`1`) —
     *   `throw(error)` was called: cancel the collection and reject the promise with the error.
     * - [FlowAsyncIteratorCommand.MUST_RETURN] (`2`) —
     *   `return(value)` was called: cancel the collection and resolve the promise with `{ done: true, value }`.
     *
     * @see [FlowAsyncIteratorCommand]
     */
    val command: FlowAsyncIteratorCommand.CommandType

    /**
     * The argument that accompanied the JavaScript call which produced this request.
     * Its meaning depends on [command]:
     * - [FlowAsyncIteratorCommand.NEXT_ELEMENT]: unused, always `undefined`.
     * - [FlowAsyncIteratorCommand.MUST_THROW]: the error passed to `throw(error)`, an arbitrary JavaScript value
     *   (not necessarily a [Throwable]); read it via [valueToThrow].
     * - [FlowAsyncIteratorCommand.MUST_RETURN]: the value passed to `return(value)`, an arbitrary JavaScript value
     *   (or `undefined` if none was given) that is relayed as the `value` of the final `{ done: true }` result;
     *   read it via [valueToReturn].
     */
    val value: Any?
}

private object FlowAsyncIteratorCommand {
    typealias CommandType = Int
    /** `next()` was called: the flow should produce the next element. */
    const val NEXT_ELEMENT: CommandType = 0
    /** `throw(error)` was called: the collection must be canceled with the given error. */
    const val MUST_THROW: CommandType = 1
    /** `return(value)` was called: the collection must be canceled and complete with the given value. */
    const val MUST_RETURN: CommandType = 2
}

@Suppress("INVISIBLE_REFERENCE") @kotlin.internal.InlineOnly
private inline fun <T> FlowAsyncIteratorResolution(
    noinline resolve: (JsIteratorResult<T>) -> Unit,
    noinline reject: (JsPromiseError) -> Unit,
    command: FlowAsyncIteratorCommand.CommandType,
    value: Any?
): FlowAsyncIteratorResolution<T> = js("{ resolve: resolve, reject: reject, command: command, value: value }")
