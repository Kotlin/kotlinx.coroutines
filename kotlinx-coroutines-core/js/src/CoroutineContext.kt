/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.browser.*
import kotlin.coroutines.*

private external val navigator: dynamic
private const val UNDEFINED = "undefined"
internal external val process: dynamic

internal actual fun createDefaultDispatcher(): CoroutineDispatcher = when {
    // Check if we are running under ReactNative. We have to use NodeDispatcher under it.
    // The problem is that ReactNative has a `window` object with `addEventListener`, but it does not  really work.
    // For details see https://github.com/Kotlin/kotlinx.coroutines/issues/236
    // The check for ReactNative is based on https://github.com/facebook/react-native/commit/3c65e62183ce05893be0822da217cb803b121c61
    jsTypeOf(navigator) != UNDEFINED && navigator != null && navigator.product == "ReactNative" ->
        NodeDispatcher
    // Check if we are running under jsdom. WindowDispatcher doesn't work under jsdom because it accesses MessageEvent#source.
    // It is not implemented in jsdom, see https://github.com/jsdom/jsdom/blob/master/Changelog.md
    // "It's missing a few semantics, especially around origins, as well as MessageEvent source."
    isJsdom() -> NodeDispatcher
    // Check if we are in the browser and must use window.postMessage to avoid setTimeout throttling
    jsTypeOf(window) != UNDEFINED && window.asDynamic() != null && jsTypeOf(window.asDynamic().addEventListener) != UNDEFINED ->
        window.asCoroutineDispatcher()
    // If process is undefined (e.g. in NativeScript, #1404), use SetTimeout-based dispatcher
    jsTypeOf(process) == UNDEFINED -> SetTimeoutDispatcher
    // Fallback to NodeDispatcher when browser environment is not detected
    else -> NodeDispatcher
}

private fun isJsdom() = jsTypeOf(navigator) != UNDEFINED &&
    navigator != null &&
    navigator.userAgent != null &&
    jsTypeOf(navigator.userAgent) != UNDEFINED &&
    jsTypeOf(navigator.userAgent.match) != UNDEFINED &&
    navigator.userAgent.match("\\bjsdom\\b")

internal actual val DefaultDelay: Delay
    get() = Dispatchers.Default as Delay

public actual fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = coroutineContext + context
    return if (combined !== Dispatchers.Default && combined[ContinuationInterceptor] == null)
        combined + Dispatchers.Default else combined
}

// No debugging facilities on JS
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T = block()
internal actual inline fun <T> withContinuationContext(continuation: Continuation<*>, countOrElement: Any?, block: () -> T): T = block()
internal actual fun Continuation<*>.toDebugString(): String = toString()
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on JS

internal actual class UndispatchedCoroutine<in T> actual constructor(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {
    override fun afterResume(state: Any?) = uCont.resumeWith(recoverResult(state, uCont))
}
