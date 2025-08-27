package kotlinx.coroutines.internal

import kotlinx.coroutines.*

internal expect interface JsAny

internal expect fun Throwable.toJsException(): JsAny

/*
 * Schedule an exception to be thrown inside JS or Wasm/JS event loop,
 * rather than in the current execution branch.
 */
internal fun throwAsync(e: JsAny): Unit = js("setTimeout(function () { throw e }, 0)")
