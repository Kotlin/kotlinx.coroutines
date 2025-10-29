package kotlinx.coroutines

@OptIn(ExperimentalWasmJsInterop::class)
internal actual fun JsPromiseError.toThrowable(): Throwable = try {
    unsafeCast<JsReference<Throwable>>().get()
} catch (_: Throwable) {
    Exception("Non-Kotlin exception $this of type '${this::class}'")
}

@OptIn(ExperimentalWasmJsInterop::class)
internal actual fun Throwable.toJsPromiseError(): JsPromiseError = toJsReference()
