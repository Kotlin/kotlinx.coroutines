package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

@PublishedApi // to have unmangled name when using from other modules via suppress
@Suppress("PropertyName")
internal expect val DefaultDelay: Delay

internal expect fun Continuation<*>.toDebugString(): String
internal expect val CoroutineContext.coroutineName: String?
internal expect fun wrapContextWithDebug(context: CoroutineContext): CoroutineContext

/**
 * Executes a block using a given coroutine context.
 * @param countOrElement pre-cached value for [updateThreadContext]
 */
internal inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T {
    val oldValue = updateThreadContext(context, countOrElement)
    try {
        return block()
    } finally {
        restoreThreadContext(context, oldValue)
    }
}

/**
 * Executes a block using a context of a given continuation.
 * @param countOrElement pre-cached value for [updateThreadContext]
 */
internal inline fun <T> withContinuationContext(continuation: Continuation<*>, countOrElement: Any?, block: () -> T): T {
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

private fun Continuation<*>.updateUndispatchedCompletion(context: CoroutineContext, oldValue: Any?): UndispatchedCoroutine<*>? {
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

private tailrec fun CoroutineStackFrame.undispatchedCompletion(): UndispatchedCoroutine<*>? {
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
internal object UndispatchedMarker: CoroutineContext.Element, CoroutineContext.Key<UndispatchedMarker> {
    override val key: CoroutineContext.Key<*>
        get() = this
}

/**
 * Creates a context for a new coroutine. It installs [Dispatchers.Default] when no other dispatcher or
 * [ContinuationInterceptor] is specified and
 */
@ExperimentalCoroutinesApi
public fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = foldCopies(coroutineContext, context, true)
    val debug = wrapContextWithDebug(combined)
    return if (combined !== Dispatchers.Default && combined[ContinuationInterceptor] == null)
        debug + Dispatchers.Default else debug
}

/**
 * Creates a context for coroutine builder functions that do not launch a new coroutine, e.g. [withContext].
 * @suppress
 */
@InternalCoroutinesApi
public fun CoroutineContext.newCoroutineContext(addedContext: CoroutineContext): CoroutineContext {
    /*
     * Fast-path: we only have to copy/merge if 'addedContext' (which typically has one or two elements)
     * contains copyable elements.
     */
    if (!addedContext.hasCopyableElements()) return this + addedContext
    return foldCopies(this, addedContext, false)
}

private fun CoroutineContext.hasCopyableElements(): Boolean =
    fold(false) { result, it -> result || it is CopyableThreadContextElement<*> }

/**
 * Folds two contexts properly applying [CopyableThreadContextElement] rules when necessary.
 * The rules are the following:
 * - If neither context has CTCE, the sum of two contexts is returned
 * - Every CTCE from the left-hand side context that does not have a matching (by key) element from right-hand side context
 *   is [copied][CopyableThreadContextElement.copyForChild] if [isNewCoroutine] is `true`.
 * - Every CTCE from the left-hand side context that has a matching element in the right-hand side context is [merged][CopyableThreadContextElement.mergeForChild]
 * - Every CTCE from the right-hand side context that hasn't been merged is copied
 * - Everything else is added to the resulting context as is.
 */
private fun foldCopies(originalContext: CoroutineContext, appendContext: CoroutineContext, isNewCoroutine: Boolean): CoroutineContext {
    // Do we have something to copy left-hand side?
    val hasElementsLeft = originalContext.hasCopyableElements()
    val hasElementsRight = appendContext.hasCopyableElements()

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
