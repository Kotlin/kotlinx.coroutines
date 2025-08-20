package kotlinx.coroutines.internal

import kotlin.js.unsafeCast

internal actual external interface JsAny

internal actual fun Throwable.toJsException(): JsAny = this.unsafeCast<JsAny>()

internal actual fun propagateExceptionFinalResort(exception: Throwable) {
    throwAsync(exception.toJsException())
}
