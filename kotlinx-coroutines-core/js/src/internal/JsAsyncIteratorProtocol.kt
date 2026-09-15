@file:OptIn(ExperimentalStdlibApi::class)
package kotlinx.coroutines.internal

import kotlinx.js.JsPlainObject
import kotlin.js.Promise

@JsPlainObject
@JsName("IteratorResult")
internal external interface JsIteratorResult<out T> {
    public val value: T?
    public val done: Boolean
}

@JsPlainObject
@JsName("AsyncIterator")
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Iteration_protocols#the_async_iterator_and_async_iterable_protocols
internal external interface JsAsyncIterator<out T> {
    public val next: () -> Promise<JsIteratorResult<T>>
    // `return` and `throw` must be able to accept either zero arguments or a single one
    public val `return`: (value: @UnsafeVariance T?) -> Promise<JsIteratorResult<T>>
    public val `throw`: (value: Any?) -> Promise<JsIteratorResult<T>>
}

@JsPlainObject
@JsName("AsyncIterableIterator")
internal external interface JsAsyncIterableIterator<out T> : JsAsyncIterator<T>

@JsName("AsyncIterable")
internal external interface JsAsyncIterable<out T> {
    @JsSymbol("asyncIterator")
    public fun asyncIterator(): JsAsyncIterator<T>
}
