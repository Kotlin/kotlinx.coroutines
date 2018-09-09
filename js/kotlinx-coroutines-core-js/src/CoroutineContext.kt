/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.browser.*
import kotlin.coroutines.experimental.*

private external val navigator: dynamic
private const val UNDEFINED = "undefined"

@Suppress("PropertyName", "UnsafeCastFromDynamic")
public actual val DefaultDispatcher: CoroutineDispatcher = when {
    // Check if we are running under ReactNative. We have to use NodeDispatcher under it.
    // The problem is that ReactNative has a `window` object with `addEventListener`, but it does not  really work.
    // For details see https://github.com/Kotlin/kotlinx.coroutines/issues/236
    // The check for ReactNative is based on https://github.com/facebook/react-native/commit/3c65e62183ce05893be0822da217cb803b121c61
    jsTypeOf(navigator) != UNDEFINED && navigator != null && navigator.product == "ReactNative" ->
        NodeDispatcher()
    // Check if we are in the browser and must use window.postMessage to avoid setTimeout throttling
    jsTypeOf(window) != UNDEFINED && window.asDynamic() != null && jsTypeOf(window.asDynamic().addEventListener) != UNDEFINED ->
        window.asCoroutineDispatcher()
    // Fallback to NodeDispatcher when browser environment is not detected
    else -> NodeDispatcher()
}

internal actual val DefaultDelay: Delay = DefaultDispatcher as Delay

/**
 * Creates context for the new coroutine. It installs [DefaultDispatcher] when no other dispatcher nor
 * [ContinuationInterceptor] is specified, and adds optional support for debugging facilities (when turned on).
 */
@Suppress("ACTUAL_FUNCTION_WITH_DEFAULT_ARGUMENTS")
public actual fun newCoroutineContext(context: CoroutineContext, parent: Job? = null): CoroutineContext {
    val wp = if (parent == null) context else context + parent
    return if (context !== DefaultDispatcher && context[ContinuationInterceptor] == null)
        wp + DefaultDispatcher else wp
}

// No debugging facilities on JS
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, block: () -> T): T = block()
internal actual fun Continuation<*>.toDebugString(): String = toString()
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on JS
