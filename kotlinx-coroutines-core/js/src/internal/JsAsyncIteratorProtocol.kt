@file:OptIn(ExperimentalStdlibApi::class)
package kotlinx.coroutines.internal

import kotlinx.js.JsPlainObject
import kotlin.js.Promise

@JsPlainObject
@JsName("AsyncIterator")
internal external interface JsAsyncIterator<out T> {
    public val next: () -> Promise<JsIteratorResult<T>>
    public val `return`: () -> Promise<JsIteratorResult<T>>
    public val `throw`: (value: Any?) -> Promise<JsIteratorResult<T>>
}

@JsPlainObject
@JsName("IteratorResult")
internal external interface JsIteratorResult<out T> {
    public val value: T?
    public val done: Boolean
}

@JsName("AsyncIterable")
internal external interface JsAsyncIterable<out T> {
    @JsSymbol("asyncIterator")
    public fun asyncIterator(): JsAsyncIterator<T>
}
