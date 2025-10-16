package kotlinx.coroutines

import kotlin.js.*

@OptIn(ExperimentalWasmJsInterop::class)
internal external interface JsProcess : JsAny {
    fun nextTick(handler: () -> Unit)
}

@OptIn(ExperimentalWasmJsInterop::class)
internal fun tryGetProcess(): JsProcess? =
    js("(typeof(process) !== 'undefined' && typeof(process.nextTick) === 'function') ? process : null")

@OptIn(ExperimentalWasmJsInterop::class)
internal fun tryGetWindow(): W3CWindow? =
    js("(typeof(window) !== 'undefined' && window != null && typeof(window.addEventListener) === 'function') ? window : null")

internal actual fun createDefaultDispatcher(): CoroutineDispatcher =
    tryGetProcess()?.let(::NodeDispatcher)
        ?: tryGetWindow()?.let(::WindowDispatcher)
        ?: SetTimeoutDispatcher
