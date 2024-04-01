package kotlinx.coroutines

import org.w3c.dom.*

internal external interface JsProcess : JsAny {
    fun nextTick(handler: () -> Unit)
}

internal fun tryGetProcess(): JsProcess? =
    js("(typeof(process) !== 'undefined' && typeof(process.nextTick) === 'function') ? process : null")

internal fun tryGetWindow(): Window? =
    js("(typeof(window) !== 'undefined' && window != null && typeof(window.addEventListener) === 'function') ? window : null")

internal actual fun createDefaultDispatcher(): CoroutineDispatcher =
    tryGetProcess()?.let(::NodeDispatcher)
        ?: tryGetWindow()?.let(::WindowDispatcher)
        ?: SetTimeoutDispatcher
