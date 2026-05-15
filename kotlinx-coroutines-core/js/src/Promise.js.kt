package kotlinx.coroutines

@Suppress("USELESS_CAST") // on JS, arbitrary objects can be thrown
@OptIn(ExperimentalWasmJsInterop::class)
internal actual fun JsPromiseError.toThrowable(): Throwable = this as? Throwable ?:
    Exception("Promise resolved with a non-Throwable exception '$this' (type ${this::class})")

@OptIn(ExperimentalWasmJsInterop::class)
internal actual fun Throwable.toJsPromiseError(): JsPromiseError = this
