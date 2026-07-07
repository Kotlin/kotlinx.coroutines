package kotlinx.coroutines

import kotlinx.browser.*

private const val UNDEFINED = "undefined"

internal actual fun tryGetTestWindow(): W3CWindow? =
    if (jsTypeOf(window) != UNDEFINED && window.asDynamic() != null &&
        jsTypeOf(window.asDynamic().addEventListener) != UNDEFINED &&
        jsTypeOf(window.asDynamic().requestAnimationFrame) != UNDEFINED
    ) window else null
