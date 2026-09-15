@file:OptIn(
    ExperimentalJsExport::class,
    ExperimentalJsStatic::class,
    ExperimentalWasmJsInterop::class,
    ExperimentalStdlibApi::class
)
@file:Suppress("INVISIBLE_REFERENCE", "EXPOSED_FUNCTION_RETURN_TYPE", "EXPOSED_PARAMETER_TYPE")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.JsAsyncIterable
import kotlinx.coroutines.internal.JsAsyncIterableIterator
import kotlinx.coroutines.internal.JsAsyncIterator
import kotlinx.coroutines.internal.JsIteratorResult
import kotlinx.coroutines.internal.JsOptionalExport
import kotlinx.js.JsPlainObject
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.coroutineContext
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
        var isClosed = false
        var collectionJob: Job? = null
        var undeliveredError: Throwable? = null
        val pendingNextRequests: JsArrayDeque<PromiseResolution<JsIteratorResult<T>>> = js("[]")
        var producerContinuation: CancellableContinuation<Unit>? = null
        @Suppress("NOTHING_TO_INLINE")
        inline fun takeUndeliveredError(): Throwable? = undeliveredError.also { undeliveredError = null }
        fun completePendingRequests() {
            while (pendingNextRequests.length != 0) {
                pendingNextRequests.shift().resolve(JsIteratorResult(done = true))
            }
        }
        suspend fun emitValue(value: T) {
            coroutineContext.ensureActive()
            pendingNextRequests.shift().resolve(JsIteratorResult(value = value, done = false))
            if (pendingNextRequests.length == 0) {
                try {
                    suspendCancellableCoroutine { producerContinuation = it }
                } finally {
                    producerContinuation = null
                }
            }
        }
        fun onFlowCompleted(cause: Throwable?) {
            isClosed = true
            if (cause != null && cause !is CancellationException) {
                if (pendingNextRequests.length != 0) {
                    pendingNextRequests.shift().reject(cause.toJsPromiseError())
                } else {
                    undeliveredError = cause
                }
            }
            completePendingRequests()
        }
        // Reports the cleanup error only if the collection was still running, so that a repeated `return`/`throw`
        // or a call after the flow has failed doesn't re-report an already delivered exception
        fun close(cancellation: CancellationException, onClosed: (cleanupError: Throwable?) -> Unit) {
            isClosed = true
            completePendingRequests()
            val job = collectionJob
            if (job == null || job.isCompleted) {
                onClosed(null)
            } else {
                job.cancel(cancellation)
                job.invokeOnCompletion { onClosed(takeUndeliveredError()) }
            }
        }
        val iterator = JsAsyncIterator<T>(
            next = {
                if (isClosed) {
                    val error = takeUndeliveredError()
                    return@JsAsyncIterator if (error != null) {
                        Promise.reject(error.toJsPromiseError())
                    } else {
                        Promise.resolve(JsIteratorResult(done = true))
                    }
                }
                Promise { resolve, reject ->
                    pendingNextRequests.push(PromiseResolution(resolve, reject))
                    val continuation = producerContinuation
                    if (collectionJob == null) {
                        collectionJob = GlobalScope.launch(start = CoroutineStart.UNDISPATCHED) {
                            try {
                                collect(::emitValue)
                                onFlowCompleted(null)
                            } catch (e: Throwable) {
                                onFlowCompleted(e)
                            }
                        }
                    } else if (continuation != null) {
                        producerContinuation = null
                        // Resume synchronously to run the flow up to the next element right inside `next()`,
                        // consistently with the undispatched start
                        continuation.resumeProducerUndispatched()
                    }
                }
            },
            `return` = { value ->
                Promise { resolve, reject ->
                    close(CancellationException("Flow collection was closed via AsyncIterator#return method")) { cleanupError ->
                        if (cleanupError != null) {
                            reject(cleanupError.toJsPromiseError())
                        } else {
                            resolve(JsIteratorResult(value = value, done = true))
                        }
                    }
                }
            },
            `throw` = { err: dynamic ->
                val cause = err.unsafeCast<JsPromiseError>().toThrowableOrNull()
                val cancellation = cause as? CancellationException
                    ?: CancellationException("Flow collection was closed via AsyncIterator#throw method", cause)
                Promise { _, reject ->
                    close(cancellation) { cleanupError ->
                        reject(cleanupError?.toJsPromiseError() ?: err)
                    }
                }
            }
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

@JsPlainObject
internal external interface PromiseResolution<T> {
    val resolve: (T) -> Unit
    val reject: (JsPromiseError) -> Unit
}
