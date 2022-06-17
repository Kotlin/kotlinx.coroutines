/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.browser.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

private external val navigator: dynamic
private const val UNDEFINED = "undefined"
internal external val process: dynamic

internal fun createDefaultDispatcher(): CoroutineDispatcher = when {
    // Check if we are running under jsdom. WindowDispatcher doesn't work under jsdom because it accesses MessageEvent#source.
    // It is not implemented in jsdom, see https://github.com/jsdom/jsdom/blob/master/Changelog.md
    // "It's missing a few semantics, especially around origins, as well as MessageEvent source."
    isJsdom() -> NodeDispatcher
    // Check if we are in the browser and must use window.postMessage to avoid setTimeout throttling
    jsTypeOf(window) != UNDEFINED && window.asDynamic() != null && jsTypeOf(window.asDynamic().addEventListener) != UNDEFINED ->
        window.asCoroutineDispatcher()
    // If process is undefined (e.g. in NativeScript, #1404), use SetTimeout-based dispatcher
    jsTypeOf(process) == UNDEFINED || jsTypeOf(process.nextTick) == UNDEFINED -> SetTimeoutDispatcher
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

public actual fun CoroutineContext.newCoroutineContext(addedContext: CoroutineContext): CoroutineContext {
    return this + addedContext
}

// No debugging facilities on JS
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T {
    val oldValue = updateThreadContext(context, countOrElement)
    try {
        return block()
    } finally {
        restoreThreadContext(context, oldValue)
    }
}

internal actual inline fun <T> withContinuationContext(continuation: Continuation<*>, countOrElement: Any?, block: () -> T): T {
    val context = continuation.context
    val oldValue = updateThreadContext(context, countOrElement)
    val undispatchedCompletion = if (oldValue !== NO_THREAD_ELEMENTS) {
        // Only if some values were replaced we'll go to the slow path of figuring out where/how to restore them
        continuation.updateUndispatchedCompletion(context, oldValue)
    } else {
        null // fast path -- don't even try to find undispatchedCompletion as there's nothing to restore in the context
    }
    try {
        return block()
    } finally {
        if (undispatchedCompletion == null || undispatchedCompletion.clearThreadContext()) {
            restoreThreadContext(context, oldValue)
        }
    }
}

private object UndispatchedMarker: CoroutineContext.Element, CoroutineContext.Key<UndispatchedMarker> {
    override val key: CoroutineContext.Key<*>
        get() = this
}

internal tailrec fun CoroutineStackFrame.undispatchedCompletion(): UndispatchedCoroutine<*>? {
    // Find direct completion of this continuation
    val completion: CoroutineStackFrame = when (this) {
        is DispatchedCoroutine<*> -> return null
        else -> callerFrame ?: return null // something else -- not supported
    }
    if (completion is UndispatchedCoroutine<*>) return completion // found UndispatchedCoroutine!
    return completion.undispatchedCompletion() // walk up the call stack with tail call
}

internal fun Continuation<*>.updateUndispatchedCompletion(context: CoroutineContext, oldValue: Any?): UndispatchedCoroutine<*>? {
    if (this !is CoroutineStackFrame) return null
    /*
     * Fast-path to detect whether we have undispatched coroutine at all in our stack.
     *
     * Implementation note.
     * If we ever find that stackwalking for thread-locals is way too slow, here is another idea:
     * 1) Store undispatched coroutine right in the `UndispatchedMarker` instance
     * 2) To avoid issues with cross-dispatch boundary, remove `UndispatchedMarker`
     *    from the context when creating dispatched coroutine in `withContext`.
     *    Another option is to "unmark it" instead of removing to save an allocation.
     *    Both options should work, but it requires more careful studying of the performance
     *    and, mostly, maintainability impact.
     */
    val potentiallyHasUndispatchedCoroutine = context[UndispatchedMarker] !== null
    if (!potentiallyHasUndispatchedCoroutine) return null
    val completion = undispatchedCompletion()
    completion?.saveThreadContext(context, oldValue)
    return completion
}

internal actual fun Continuation<*>.toDebugString(): String = toString()
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on JS

internal actual class UndispatchedCoroutine<in T> actual constructor(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {

    private var threadStateToRecover : Pair<CoroutineContext, Any?>? = null

    init {
        val values = updateThreadContext(context, null)
        restoreThreadContext(context, values)
        saveThreadContext(context, values)
    }

    fun saveThreadContext(context: CoroutineContext, oldValue: Any?) {
        threadStateToRecover = context to oldValue
    }

    fun clearThreadContext(): Boolean {
        if (threadStateToRecover == null) return false
        threadStateToRecover = null
        return true
    }

    override fun afterResume(state: Any?) {
        threadStateToRecover?.let { (ctx, value) ->
            restoreThreadContext(ctx, value)
            threadStateToRecover = null
        }
        // resume undispatched -- update context but stay on the same dispatcher
        val result = recoverResult(state, uCont)
        withContinuationContext(uCont, null) {
            uCont.resumeWith(result)
        }
        //uCont.resumeWith(recoverResult(state, uCont))
    }
}
