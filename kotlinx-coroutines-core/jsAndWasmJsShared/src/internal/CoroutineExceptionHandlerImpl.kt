package kotlinx.coroutines.internal

import kotlinx.coroutines.*

internal expect interface JsAny

internal expect fun Throwable.toJsException(): JsAny

internal fun throwAsync(e: JsAny): Unit = js("setTimeout(function () { throw e }, 0)")

internal actual fun propagateExceptionFinalResort(exception: Throwable) {
    throwAsync(exception.toJsException())

}
