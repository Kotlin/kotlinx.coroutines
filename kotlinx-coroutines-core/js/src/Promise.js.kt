package kotlinx.coroutines

@Suppress("USELESS_CAST")
@OptIn(ExperimentalWasmJsInterop::class)
// The cast looks redundant, but the `JsPromiseError` being a type alias to `Throwable` is actually incorrect.
// A promise can be rejected with any value, not just `Throwable`.
internal actual fun JsPromiseError.toThrowableOrNull(): Throwable? =
    this as? Throwable

@OptIn(ExperimentalWasmJsInterop::class)
internal actual fun Throwable.toJsPromiseError(): JsPromiseError = this
