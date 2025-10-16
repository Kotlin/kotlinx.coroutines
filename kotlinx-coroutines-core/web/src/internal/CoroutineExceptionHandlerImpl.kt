package kotlinx.coroutines.internal

import kotlin.js.*

/*
 * Schedule an exception to be thrown inside JS or Wasm/JS event loop,
 * rather than in the current execution branch.
 */
@OptIn(ExperimentalWasmJsInterop::class)
internal fun throwAsyncJsError(message: String?, className: String?, stack: String?) {
    js("""
        var error = new Error();
        error.message = message;
        error.name = className;
        error.stack = stack;
        setTimeout(function () { throw error }, 0);
    """)
}

internal actual fun propagateExceptionFinalResort(exception: Throwable) = with(exception) {
    throwAsyncJsError(message, this::class.simpleName, stackTraceToString())
}