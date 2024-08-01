package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.CoroutineStackFrame
import kotlinx.coroutines.internal.NO_THREAD_ELEMENTS
import kotlinx.coroutines.internal.ScopeCoroutine
import kotlinx.coroutines.internal.restoreThreadContext
import kotlinx.coroutines.internal.updateThreadContext
import kotlin.coroutines.*
import kotlin.jvm.*

@PublishedApi // Used from kotlinx-coroutines-test via suppress, not part of ABI
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

// No debugging facilities on Wasm and JS
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

internal tailrec fun CoroutineStackFrame.undispatchedCompletion(): UndispatchedCoroutine<*>? {
    // Find direct completion of this continuation
    val completion: CoroutineStackFrame = when (this) {
        is DispatchedCoroutine<*> -> return null
        else -> callerFrame ?: return null // something else -- not supported
    }
    if (completion is UndispatchedCoroutine<*>) return completion // found UndispatchedCoroutine!
    return completion.undispatchedCompletion() // walk up the call stack with tail call
}

/**
 * Marker indicating that [UndispatchedCoroutine] exists somewhere up in the stack.
 * Used as a performance optimization to avoid stack walking where it is not necessary.
 */
private object UndispatchedMarker: CoroutineContext.Element, CoroutineContext.Key<UndispatchedMarker> {
    override val key: CoroutineContext.Key<*>
        get() = this
}

internal actual fun Continuation<*>.toDebugString(): String = toString()
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on Wasm and JS

internal actual class UndispatchedCoroutine<in T> actual constructor(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {

    private var savedContext: CoroutineContext? = null
    private var savedOldValue: Any? = null

    fun saveThreadContext(context: CoroutineContext, oldValue: Any?) {
        savedContext = context
        savedOldValue = oldValue
    }

    fun clearThreadContext(): Boolean {
        if (savedContext == null) return false
        savedContext = null
        savedOldValue = null
        return true
    }

    override fun afterResume(state: Any?) {
        savedContext?.let { context ->
            restoreThreadContext(context, savedOldValue)
            savedContext = null
            savedOldValue = null
        }
        // resume undispatched -- update context but stay on the same dispatcher
        val result = recoverResult(state, uCont)
        withContinuationContext(uCont, null) {
            uCont.resumeWith(result)
        }
    }
}
