// This file should be a part of `CoroutineContext.common.kt`, but adding `JvmName` to that fails: KT-75248
@file:JvmName("CoroutineContextKt")
@file:JvmMultifileClass
package kotlinx.coroutines

import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.jvm.JvmMultifileClass
import kotlin.jvm.JvmName

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
