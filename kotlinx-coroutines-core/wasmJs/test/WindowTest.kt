package kotlinx.coroutines

import kotlin.js.*

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
private fun hasRequestAnimationFrame(window: W3CWindow): Boolean =
    js("typeof window.requestAnimationFrame === 'function'")

internal actual fun tryGetTestWindow(): W3CWindow? =
    tryGetWindow()?.takeIf(::hasRequestAnimationFrame)
