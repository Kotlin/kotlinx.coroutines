/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.CoroutineStackFrame

/**
 * Creates context for the new coroutine. It installs [Dispatchers.Default] when no other dispatcher nor
 * [ContinuationInterceptor] is specified and adds support for
 * copyable thread context [elements][CopyableThreadContextElement] and debugging facilities (optionally, when turned on).
 *
 * See [DEBUG_PROPERTY_NAME] for description of debugging facilities on JVM.
 */
@ExperimentalCoroutinesApi
public actual fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = foldCopies(coroutineContext, context, true)
    val debug = if (DEBUG) combined + CoroutineId(COROUTINE_ID.incrementAndGet()) else combined
    return if (combined !== Dispatchers.Default && combined[ContinuationInterceptor] == null)
        debug + Dispatchers.Default else debug
}

/**
 * Creates context for coroutine builder functions that do not launch a new coroutine, namely [withContext].
 * @suppress
 */
@InternalCoroutinesApi
public actual fun CoroutineContext.newCoroutineContext(addedContext: CoroutineContext): CoroutineContext {
    /*
     * Fast-path: we only have to copy/merge if 'addedContext' (which typically has one or two elements)
     * contains copyable element.
     */
    if (!addedContext.fold(false, hasCopyableElements)) return this + addedContext
    return foldCopies(this, addedContext, false)
}

private val hasCopyableElements: (Boolean, CoroutineContext.Element) -> Boolean = { result, it ->
    result || it is CopyableThreadContextElement<*>
}

/**
 * Folds two contexts properly applying [CopyableThreadContextElement] rules when necessary.
 * The rules are the following:
 * * If both context do not have CTCE, the sum of two contexts is returned
 * * Every CTCE from left-hand side context that does not have matching (by key) element from right-hand side context
 *   is [copied][CopyableThreadContextElement.copyForChild]
 * * Every CTCE from left-hand side context that has matching element in right-hand side context is [merged][CopyableThreadContextElement.mergeForChild]
 * * Every CTCE from right-hand side context that hasn't been merged is copied
 * * Everything else is added to the resulting context as is.
 */
private fun foldCopies(originalContext: CoroutineContext, appendContext: CoroutineContext, isNewCoroutine: Boolean): CoroutineContext {
    // Do we have something to copy left-hand side?
    val hasElementsLeft = originalContext.fold(false, hasCopyableElements)
    val hasElementsRight = appendContext.fold(false, hasCopyableElements)

    // Nothing to fold, so just return the sum of contexts
    if (!hasElementsLeft && !hasElementsRight) {
        return originalContext + appendContext
    }

    var leftoverContext = appendContext
    val folded = originalContext.fold<CoroutineContext>(EmptyCoroutineContext) { result, element ->
        if (element !is CopyableThreadContextElement<*>) return@fold result + element
        // Will this element be overwritten?
        val newElement = leftoverContext[element.key]
        // No, just copy it
        if (newElement == null) {
            // For 'withContext'-like builders we do not copy as the element is not shared
            return@fold result + if (isNewCoroutine) element.copyForChild() else element
        }
        // Yes, then first remove the element from append context
        leftoverContext = leftoverContext.minusKey(element.key)
        // Return the sum
        @Suppress("UNCHECKED_CAST")
        return@fold result + (element as CopyableThreadContextElement<Any?>).mergeForChild(newElement)
    }

    if (hasElementsRight) {
        leftoverContext = leftoverContext.fold<CoroutineContext>(EmptyCoroutineContext) { result, element ->
            // We're appending new context element -- we have to copy it, otherwise it may be shared with others
            if (element is CopyableThreadContextElement<*>) {
                return@fold result + element.copyForChild()
            }
            return@fold result + element
        }
    }
    return folded + leftoverContext
}

/**
 * Executes a block using a given coroutine context.
 */
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T {
    val oldValue = updateThreadContext(context, countOrElement)
    try {
        return block()
    } finally {
        restoreThreadContext(context, oldValue)
    }
}

/**
 * Executes a block using a context of a given continuation.
 */
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
     * Fast-path to detect whether we have unispatched coroutine at all in our stack.
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
    val potentiallyHasUndispatchedCorotuine = context[UndispatchedMarker] !== null
    if (!potentiallyHasUndispatchedCorotuine) return null
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
 * Used as a performance optimization to avoid stack walking where it is not nesessary.
 */
private object UndispatchedMarker: CoroutineContext.Element, CoroutineContext.Key<UndispatchedMarker> {
    override val key: CoroutineContext.Key<*>
        get() = this
}

// Used by withContext when context changes, but dispatcher stays the same
internal actual class UndispatchedCoroutine<in T>actual constructor (
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(if (context[UndispatchedMarker] == null) context + UndispatchedMarker else context, uCont) {

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

internal actual val CoroutineContext.coroutineName: String? get() {
    if (!DEBUG) return null
    val coroutineId = this[CoroutineId] ?: return null
    val coroutineName = this[CoroutineName]?.name ?: "coroutine"
    return "$coroutineName#${coroutineId.id}"
}

private const val DEBUG_THREAD_NAME_SEPARATOR = " @"

@IgnoreJreRequirement // desugared hashcode implementation
internal data class CoroutineId(
    val id: Long
) : ThreadContextElement<String>, AbstractCoroutineContextElement(CoroutineId) {
    companion object Key : CoroutineContext.Key<CoroutineId>
    override fun toString(): String = "CoroutineId($id)"

    override fun updateThreadContext(context: CoroutineContext): String {
        val coroutineName = context[CoroutineName]?.name ?: "coroutine"
        val currentThread = Thread.currentThread()
        val oldName = currentThread.name
        var lastIndex = oldName.lastIndexOf(DEBUG_THREAD_NAME_SEPARATOR)
        if (lastIndex < 0) lastIndex = oldName.length
        currentThread.name = buildString(lastIndex + coroutineName.length + 10) {
            append(oldName.substring(0, lastIndex))
            append(DEBUG_THREAD_NAME_SEPARATOR)
            append(coroutineName)
            append('#')
            append(id)
        }
        return oldName
    }

    override fun restoreThreadContext(context: CoroutineContext, oldState: String) {
        Thread.currentThread().name = oldState
    }
}
