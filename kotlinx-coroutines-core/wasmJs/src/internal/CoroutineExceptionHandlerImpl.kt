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
    // https://github.com/JetBrains/kotlin-wrappers/blob/master/kotlin-browser/src/webMain/generated/web/errors/reportError.kt
    if (globalThis.reportError != null) {
        // Modern browsers, Deno, Bun, etc.
        globalThis.reportError(jsException)
    } else {
        // Old Safari, Node.js
        throwAsync(jsException)
    }
}
