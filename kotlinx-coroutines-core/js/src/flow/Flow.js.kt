@file:OptIn(ExperimentalJsExport::class, ExperimentalJsStatic::class, ExperimentalStdlibApi::class)
@file:Suppress("INVISIBLE_REFERENCE", "EXPOSED_FUNCTION_RETURN_TYPE", "EXPOSED_PARAMETER_TYPE")
package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.JsAsyncIterable
import kotlinx.coroutines.internal.JsAsyncIterator
import kotlinx.coroutines.internal.JsIteratorResult
import kotlinx.coroutines.internal.JsOptionalExport
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.js.Promise

@JsOptionalExport(couldBeConvertedToExplicitExport = true)
public actual interface Flow<out T> {
    @JsExport.Ignore
    public actual suspend fun collect(collector: FlowCollector<T>)

    /**
     * Represents [Flow] as a JavaScript [AsyncIterable](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Iteration_protocols#the_async_iterator_and_async_iterable_protocols)
     *
     * This function is a shorthand for:
     * `buffer(0).produceIn(GlobalScope)`.
     *
     * Use it when a [Flow] needs to be exposed to JavaScript APIs that consume
     * `AsyncIterable` (for example, via `for await (...)`).
     *
     * The returned iterable is backed by a coroutine started in [GlobalScope], so its lifecycle
     * is not bound to a structured coroutine scope. With `buffer(0)`, elements are relayed with
     * rendezvous-style backpressure (producer and consumer synchronize per element).
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
     * for await (const value of flow.asAsyncIterable()) {
     *   console.log(value)
     * }
     *```
     *
     * This API is experimental: behavior and lifecycle semantics may change in future releases.
     */
    @ExperimentalCoroutinesApi
    public fun asAsyncIterable(): JsAsyncIterable<T> =
        buffer(0).produceIn(GlobalScope)

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
