package kotlinx.coroutines.internal

import kotlin.js.*

/*
 * Schedule an exception to be thrown inside JS or Wasm/JS event loop,
 * rather than in the current execution branch.
 */
@OptIn(ExperimentalWasmJsInterop::class)
internal fun throwAsyncJsError(message: String?, className: String?, stack: String) {
    // reportError is the browser API for reporting unhandled exceptions
    // https://developer.mozilla.org/en-US/docs/Web/API/Window/reportError
    // https://developer.mozilla.org/en-US/docs/Web/API/WorkerGlobalScope/reportError
    // It is also implemented in some non-browser JS runtimes (Node.js alternatives)
    // Deno https://docs.deno.com/api/web/~/reportError
    // Bun https://bun.sh/reference/globals/reportError#globals.reportError
    js("""
        var error = new Error();
        error.message = message;
        error.name = className;
        error.stack = stack;
        if (typeof globalThis.reportError === 'function') {
            // Up-to-date browsers and some non-browser JS runtimes (Deno, Bun)
            globalThis.reportError(error);
        } else {
            // Fallback for old browsers (pre-2022), Node.js
            setTimeout(function () { throw error }, 0);
        }
    """)
}

internal actual fun propagateExceptionFinalResort(exception: Throwable) = with(exception) {
    throwAsyncJsError(message, this::class.simpleName, stackTraceToString())
}
