@file:OptIn(
    ExperimentalJsExport::class,
    ExperimentalJsStatic::class,
    ExperimentalWasmJsInterop::class,
    ExperimentalStdlibApi::class
)
@file:Suppress("INVISIBLE_REFERENCE", "EXPOSED_FUNCTION_RETURN_TYPE", "EXPOSED_PARAMETER_TYPE")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.ClosedSendChannelException
import kotlinx.coroutines.internal.JsAsyncIterable
import kotlinx.coroutines.internal.JsAsyncIterableIterator
import kotlinx.coroutines.internal.JsAsyncIterator
import kotlinx.coroutines.internal.JsIteratorResult
import kotlinx.coroutines.internal.JsOptionalExport
import kotlinx.coroutines.internal.`return`
import kotlin.js.Promise

@JsOptionalExport(couldBeConvertedToExplicitExport = true)
public actual interface Flow<out T> {
    @JsExport.Ignore
    public actual suspend fun collect(collector: FlowCollector<T>)

    /**
     * Represents [Flow] as a JavaScript [AsyncIterable](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Iteration_protocols#the_async_iterator_and_async_iterable_protocols)
     *
     * Use it when a [Flow] needs to be exposed to JavaScript APIs that consume
     * `AsyncIterable` (for example, via `for await (...)`).
     *
     * The flow is collected lazily: the collection starts on the first `next()` call and runs in a coroutine
     * launched in [GlobalScope] on [Dispatchers.Default]. Since there is no caller coroutine on the JavaScript side,
     * the collection has no parent [Job]: it is not cancelled together with any Kotlin scope and its lifecycle
     * is controlled solely through the iterator (`next`, `return`, `throw`). The upstream context can still be
     * configured with [flowOn].
     *
     * Elements are relayed with rendezvous-style backpressure, like in an async generator: each `next()` call
     * synchronously runs the flow until the next element is emitted (or until the flow suspends), and the flow
     * stays suspended at `emit` until the next element is requested. Nothing is buffered.
     *
     * Early exit via `return` or `throw` cancels the collection and settles the returned promise only after
     * the flow has finished its cleanup. Like in async generators, calls are queued: `return`/`throw` take effect
     * only after the previously issued `next()` calls are settled. `throw(error)` aborts the collection by throwing
     * `error` from the suspended `emit` if it is a [Throwable] (otherwise it acts like `return()`); the returned
     * promise is rejected with `error`, or with the exception thrown by the flow's cleanup, if any.
     * If the flow fails, the pending `next()` promise is rejected with the exception, and the following calls
     * report completion.
     *
     * JavaScript/TypeScript usage:
     * ```javascript
     * for await (const value of flow) {
     *   console.log(value)
     * }
     *```
     *
     * This API is experimental: behavior and lifecycle semantics may change in future releases.
     */
    @JsSymbol("asyncIterator")
    @Deprecated("", level = DeprecationLevel.HIDDEN)
    public fun asyncIterator(): JsAsyncIterableIterator<T> {
        @Suppress("NOTHING_TO_INLINE")
        inline fun resolveRequestWithoutRunning(request: FlowAsyncIteratorResolution<T>) {
            when (request.command) {
                FlowAsyncIteratorResolution.MUST_RETURN, FlowAsyncIteratorResolution.NEXT_ELEMENT -> request.resolve(JsIteratorResult(done = true))
                FlowAsyncIteratorResolution.MUST_THROW -> request.reject(request.valueToThrow)
            }
        }
        val elementRequests = Channel<FlowAsyncIteratorResolution<T>>(onUndeliveredElement = {
            resolveRequestWithoutRunning(it)
        })
        fun scheduleNextCommand(command: FlowAsyncIteratorResolution.FlowCollectionCommand, value: Any? = VOID) = Promise { resolve, reject ->
            val ourRequest = FlowAsyncIteratorResolution(resolve, reject, command, value)
            GlobalScope.launch(start = CoroutineStart.UNDISPATCHED) {
                try {
                    elementRequests.send(ourRequest)
                } catch (_: ClosedSendChannelException) {
                    resolveRequestWithoutRunning(ourRequest)
                }
            }
        }
        GlobalScope.launch(Dispatchers.Unconfined, start = CoroutineStart.UNDISPATCHED) {
            /** Receive the initial request. Until we know that some element is requested, we won't start the flow. */
            var currentRequest = elementRequests.receive()
            when (currentRequest.command) {
                FlowAsyncIteratorResolution.MUST_RETURN -> currentRequest.resolve(JsIteratorResult(done = true))
                FlowAsyncIteratorResolution.MUST_THROW -> currentRequest.reject(currentRequest.valueToThrow)
                FlowAsyncIteratorResolution.NEXT_ELEMENT -> {
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
                                FlowAsyncIteratorResolution.MUST_THROW -> {
                                    /** Let cancellation handlers know the exact exception that went through.
                                     * If there is no exception, we pretend this is a normal cancellation.
                                     * Consistency with JS doesn't force us to do anything specific,
                                     * as JS will throw `undefined` here, but we can't do that.
                                     */
                                    currentRequest.valueToThrow.toThrowableOrNull()?.let { throw it }
                                    false
                                }
                                FlowAsyncIteratorResolution.MUST_RETURN -> false
                                FlowAsyncIteratorResolution.NEXT_ELEMENT -> true
                                /* Should never happen */
                                else -> error(
                                    "Unexpected command value ${currentRequest.command}. It should be either ${
                                        FlowAsyncIteratorResolution.MUST_THROW
                                    }, ${FlowAsyncIteratorResolution.MUST_RETURN}, or ${FlowAsyncIteratorResolution.NEXT_ELEMENT}"
                                )
                            }
                        }
                        currentRequest.resolve(
                            JsIteratorResult(
                                done = true,
                                value = if (currentRequest.command == FlowAsyncIteratorResolution.MUST_RETURN) {
                                    currentRequest.valueToReturn
                                } else {
                                    VOID
                                }
                            )
                        )
                    } catch (e: dynamic) {
                        currentRequest.reject(e)
                    }
                }
            }
            elementRequests.cancel()
        }
        val iterator = JsAsyncIterator(
            next = { scheduleNextCommand(FlowAsyncIteratorResolution.NEXT_ELEMENT) },
            _return = { scheduleNextCommand(FlowAsyncIteratorResolution.MUST_RETURN, it) },
            _throw = { scheduleNextCommand(FlowAsyncIteratorResolution.MUST_THROW, it) }
        )
        iterator.asDynamic()[js("Symbol.asyncIterator")] = { iterator }
        return iterator.unsafeCast<JsAsyncIterableIterator<T>>()
    }

    @JsExport.Ignore
    // Important note: it would be much nicer to place those factory functions outside of Flow
    // so from both Kotlin and TypeScript side it could be used without importing Flow (like in `flowOf` or `flow`)
    // However, the described way of exporting factory functions forces the functions always to be exported (even if people don't use them and don't export Flow),
    // and that may cause bundle size problems (at least right now).
    // So, until the bundle size problem is solved, we keep those factory functions inside Flow, with possibility to move them outside later.
    public companion object {
        /**
         * Converts a JavaScript AsyncIterable to a Kotlin Flow.
         *
         * The resulting flow will iterate through all values produced by the async iterable.
         * If the flow collection is canceled or fails, the iterator's `return()` method (if present) will be called
         * to properly clean up the async iterable, see [fromAsyncGenerator] for the details.
         */
        @JsStatic
        @JsName("fromAsyncIterable")
        @Deprecated("", level = DeprecationLevel.HIDDEN)
        public fun <T> fromAsyncIterable(async: JsAsyncIterable<T>): Flow<T> =
            createFlowFromAsyncGenerator { async.asyncIterator() }

        /**
         * Converts a JavaScript async generator function to a Kotlin Flow.
         *
         * The generator will be invoked to get an async iterator for each collection.
         *
         * The iterator is closed as follows:
         * - When the iterator reports completion (`done: true`), it is considered finished and `return()` is not called.
         * - When `next()` fails, or the collection is canceled or fails downstream, the iterator's `return()` method
         *   is called (if it is present, as it is optional in the protocol) and the promise it returns is awaited.
         *   The original exception is then rethrown.
         * - If `return()` itself fails, its exception replaces the original one when the original is
         *   a [CancellationException]; otherwise, it is attached to the original one as a suppressed exception.
         */
        @JsStatic
        @JsName("fromAsyncGenerator")
        @Deprecated("", level = DeprecationLevel.HIDDEN)
        public fun <T> fromAsyncGenerator(generator: () -> JsAsyncIterator<T>): Flow<T> =
            createFlowFromAsyncGenerator(generator)

        /**
         * Converts a JavaScript AsyncIterator to a Kotlin Flow.
         *
         * The resulting flow emits items produced by the iterator until it reports completion.
         * If a collection is canceled or fails, the iterator's `return()` method (if present) is called
         * to close the iterator, see [fromAsyncGenerator] for the details.
         */
        @JsStatic
        @JsName("fromAsyncIterator")
        @Deprecated("", level = DeprecationLevel.HIDDEN)
        public fun <T> fromAsyncIterator(iterator: JsAsyncIterator<T>): Flow<T> =
            createFlowFromAsyncGenerator { iterator }
    }
}

private fun <T> createFlowFromAsyncGenerator(generator: () -> JsAsyncIterator<T>) = flow {
        val iterator = generator()
        while (true) {
            try {
                val result = iterator.next().await()
                if (result.done) return@flow
                emit(result.value.unsafeCast<T>())
            } catch (e: dynamic) {
                val isCancellationException = e is CancellationException
                // `return` function is optional in iterator
                // however we should always call it in case of an exception
                // to close the iterator.
                if (jsTypeOf(iterator.`return`) == "function") {
                    // We do this to not lose the exception thrown by `emit`/`next`
                    try {
                        iterator.`return`().await()
                    } catch (returnException: dynamic) {
                        if (isCancellationException) throw returnException
                        (e as? Throwable)?.addSuppressed(returnException)
                    }
                }
                if (isCancellationException && !currentCoroutineContext().isActive) {
                    return@flow
                }
                throw e
            }
        }
    }

internal val <T> FlowAsyncIteratorResolution<T>.valueToReturn: T
    inline get() = value.unsafeCast<T>()

internal val FlowAsyncIteratorResolution<*>.valueToThrow: JsPromiseError
    inline get() = value.unsafeCast<JsPromiseError>()

internal external interface FlowAsyncIteratorResolution<T> {
    val resolve: (JsIteratorResult<T>) -> Unit
    val reject: (JsPromiseError) -> Unit

    /**
     * The kind of request issued by the JavaScript side of the async iterator protocol.
     *
     * Determines what the collection loop should do next and how [value] must be interpreted.
     * One of exactly three values:
     * - [NEXT_ELEMENT] (`0`) — `next()` was called: run the flow until the next element is emitted.
     * - [MUST_THROW] (`1`) — `throw(error)` was called: cancel the collection and reject the promise with the error.
     * - [MUST_RETURN] (`2`) — `return(value)` was called: cancel the collection and resolve the promise with `{ done: true, value }`.
     *
     * @see [FlowAsyncIteratorResolution.Companion]
     */
    val command: FlowCollectionCommand

    /**
     * The argument that accompanied the JavaScript call which produced this request.
     * Its meaning depends on [command]:
     * - [NEXT_ELEMENT]: unused, always `undefined`.
     * - [MUST_THROW]: the error passed to `throw(error)`, an arbitrary JavaScript value
     *   (not necessarily a [Throwable]); read it via [valueToThrow].
     * - [MUST_RETURN]: the value passed to `return(value)`, an arbitrary JavaScript value
     *   (or `undefined` if none was given) that is relayed as the `value` of the final `{ done: true }` result;
     *   read it via [valueToReturn].
     */
    val value: Any?

    typealias FlowCollectionCommand = Int

    @Suppress("WRONG_INITIALIZER_OF_EXTERNAL_DECLARATION")
    companion object {
        /** `next()` was called: the flow should produce the next element. */
        internal const val NEXT_ELEMENT: FlowCollectionCommand = 0
        /** `throw(error)` was called: the collection must be canceled with the given error. */
        internal const val MUST_THROW: FlowCollectionCommand = 1
        /** `return(value)` was called: the collection must be canceled and complete with the given value. */
        internal const val MUST_RETURN: FlowCollectionCommand = 2
    }
}

@kotlin.internal.InlineOnly
internal inline fun <T> FlowAsyncIteratorResolution(
    noinline resolve: (JsIteratorResult<T>) -> Unit,
    noinline reject: (JsPromiseError) -> Unit,
    command: FlowAsyncIteratorResolution.FlowCollectionCommand,
    value: Any?
): FlowAsyncIteratorResolution<T> = js("{ resolve: resolve, reject: reject, command: command, value: value }")
