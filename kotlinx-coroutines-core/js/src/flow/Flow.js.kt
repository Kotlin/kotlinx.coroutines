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
import kotlinx.js.JsPlainObject
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.resume
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
     * the flow has finished its cleanup (all `finally` blocks have completed). Unlike async generators,
     * `return`/`throw` are eager: the collection is cancelled immediately, and pending `next()` promises are
     * resolved with `{ done: true }` rather than waiting for further elements. `throw(error)` cancels
     * the collection with a [CancellationException] whose cause is `error`, so the flow cannot recover from it;
     * the returned promise is rejected with `error`, or with the exception thrown by the flow's cleanup, if any.
     * If the flow fails, the pending `next()` promise is rejected with the exception, and the following calls
     * report completion.
     *
     * Kotlin usage:
     * ```
     * val flow = flowOf(1, 2, 3)
     * val asyncIterable = flow.asAsyncIterable()
     * // pass asyncIterable to JS code expecting AsyncIterable
     * ```
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
    @ExperimentalCoroutinesApi
    @JsSymbol("asyncIterator")
    public fun asAsyncIterable(): JsAsyncIterableIterator<T> {
        lateinit var mainLoopJob: Job

        @Suppress("NOTHING_TO_INLINE")
        inline fun resolveRequestWithoutRunning(request: FlowAsyncIteratorResolution<T>) {
            when (request.command) {
                FlowAsyncIteratorResolution.MUST_RETURN -> request.resolve(JsIteratorResult(done = true))
                FlowAsyncIteratorResolution.MUST_THROW -> request.reject(request.valueToThrow)
                FlowAsyncIteratorResolution.NEXT_ELEMENT -> request.resolve(JsIteratorResult(done = !mainLoopJob.isActive))
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

        fun startResolutionLoop() {
            mainLoopJob = GlobalScope.launch(Dispatchers.Unconfined, start = CoroutineStart.UNDISPATCHED) {
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

                                    /* Should never happen, but if happens, better to stop collecting */
                                    else -> true
                                }
                            }

                            currentRequest.resolve(
                                JsIteratorResult(
                                    done = true,
                                    value = if (currentRequest.command == FlowAsyncIteratorResolution.MUST_RETURN) currentRequest.valueToReturn else VOID
                                )
                            )
                        } catch (e: dynamic) {
                            currentRequest.reject(e)
                        }
                    }
                }

                elementRequests.cancel()
            }
        }

        val iterator = JsAsyncIterator<T>(
            next = { scheduleNextCommand(FlowAsyncIteratorResolution.NEXT_ELEMENT) },
            `return` = { scheduleNextCommand(FlowAsyncIteratorResolution.MUST_RETURN, it) },
            `throw` = { scheduleNextCommand(FlowAsyncIteratorResolution.MUST_THROW, it) }
        )

        iterator.asDynamic()[js("Symbol.asyncIterator")] = { iterator }
        startResolutionLoop()

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
         * If the flow collection is canceled or fails, the iterator's `return()` method will be called
         * to properly clean up the async iterable.
         */
        @JsStatic
        @ExperimentalCoroutinesApi
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
        @ExperimentalCoroutinesApi
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
                    emit(result.value.unsafeCast<T>())
                }
            } finally {
                if (!completed) {
                    iterator.asDynamic().`return`().unsafeCast<Promise<*>>().await()
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
        @ExperimentalCoroutinesApi
        public fun <T> from(iterator: JsAsyncIterator<T>): Flow<T> =
            from { iterator }
    }
}

private fun CancellableContinuation<Unit>.resumeProducerUndispatched() {
    val dispatcher = context[ContinuationInterceptor] as? CoroutineDispatcher
    if (dispatcher != null) {
        dispatcher.resumeUndispatched(Unit)
    } else {
        resume(Unit)
    }
}

private external interface JsArrayDeque<T> {
    val length: Int
    fun push(value: T)
    fun shift(): T
}

internal val <T> FlowAsyncIteratorResolution<T>.valueToReturn: T
    inline get() = value.unsafeCast<T>()

internal val FlowAsyncIteratorResolution<*>.valueToThrow: JsPromiseError
    inline get() = value.unsafeCast<JsPromiseError>()

@JsPlainObject
internal external interface FlowAsyncIteratorResolution<T> {
    val resolve: (JsIteratorResult<T>) -> Unit
    val reject: (JsPromiseError) -> Unit
    val command: FlowCollectionCommand
    val value: Any?

    typealias FlowCollectionCommand = Int

    @Suppress("WRONG_INITIALIZER_OF_EXTERNAL_DECLARATION")
    companion object {
        internal const val NEXT_ELEMENT: FlowCollectionCommand = 0
        internal const val MUST_THROW: FlowCollectionCommand = 1
        internal const val MUST_RETURN: FlowCollectionCommand = 2

    }
}
