package kotlinx.coroutines.internal

internal actual typealias JsAny = kotlin.js.JsAny

internal external val reportError: ((error: JsAny) -> Unit)?

internal actual fun Throwable.toJsException(): JsAny =
    toJsError(message, this::class.simpleName, stackTraceToString())

internal fun toJsError(message: String?, className: String?, stack: String?): JsAny {
    js("""
    const error = new Error();
    error.message = message;
    error.name = className;
    error.stack = stack;
    return error;
    """)
}

internal actual fun propagateExceptionFinalResort(exception: Throwable) {
    val jsException = exception.toJsException()
    if (reportError != null) {
        // In Node.js runtime, use reportError.
        reportError(jsException)
    } else {
        throwAsync(jsException)
    }
}
