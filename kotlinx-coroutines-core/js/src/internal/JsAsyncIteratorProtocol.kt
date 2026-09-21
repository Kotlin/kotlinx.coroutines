@file:OptIn(ExperimentalStdlibApi::class)
@file:Suppress("INVISIBLE_REFERENCE")
package kotlinx.coroutines.internal

import kotlin.js.Promise

@JsName("IteratorResult")
internal external interface JsIteratorResult<out T> {
    public val value: T?
    public val done: Boolean
}

@kotlin.internal.InlineOnly
internal inline fun <T> JsIteratorResult(value: T? = VOID, done: Boolean): JsIteratorResult<T> =
    js("{ value: value, done: done }")

@JsName("AsyncIterator")
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Iteration_protocols#the_async_iterator_and_async_iterable_protocols
internal external interface JsAsyncIterator<out T> {
    public val next: () -> Promise<JsIteratorResult<T>>
    // `return` and `throw` must be able to accept either zero arguments or a single one
    public val `return`: (value: @UnsafeVariance T?) -> Promise<JsIteratorResult<T>>
    public val `throw`: (value: Any?) -> Promise<JsIteratorResult<T>>
}

@kotlin.internal.InlineOnly
internal inline fun <T> JsAsyncIterator(
    noinline next: () -> Promise<JsIteratorResult<T>>,
    noinline _return: (value: @UnsafeVariance T?) -> Promise<JsIteratorResult<T>>,
    noinline _throw: (value: Any?) -> Promise<JsIteratorResult<T>>,
): JsIteratorResult<T> = js("{ next: next, 'return': _return, 'throw': _throw }")

@JsName("AsyncIterableIterator")
internal external interface JsAsyncIterableIterator<out T> : JsAsyncIterator<T>

@JsName("AsyncIterable")
internal external interface JsAsyncIterable<out T> {
    @JsSymbol("asyncIterator")
    public fun asyncIterator(): JsAsyncIterator<T>
}
