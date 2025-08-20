package kotlinx.coroutines.internal

internal actual typealias JsAny = kotlin.js.JsAny

internal external object globalThis : JsAny {
    val reportError: ((error: JsAny) -> Unit)?
}

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
    if (globalThis.reportError != null) {
        // modern browsers, Deno
        globalThis.reportError(jsException)
    } else {
        // Node.js, old Safari
        throwAsync(jsException)
    }
}
