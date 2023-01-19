/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.CoroutineStackFrame

/**
 * Creates a context for a new coroutine. It installs [Dispatchers.Default] when no other dispatcher or
 * [ContinuationInterceptor] is specified and adds optional support for debugging facilities (when turned on)
 * and copyable-thread-local facilities on JVM.
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
 * Creates a context for coroutine builder functions that do not launch a new coroutine, e.g. [withContext].
 * @suppress
 */
@InternalCoroutinesApi
public actual fun CoroutineContext.newCoroutineContext(addedContext: CoroutineContext): CoroutineContext {
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
 * * If neither context has CTCE, the sum of two contexts is returned
 * * Every CTCE from the left-hand side context that does not have a matching (by key) element from right-hand side context
 *   is [copied][CopyableThreadContextElement.copyForChild] if [isNewCoroutine] is `true`.
 * * Every CTCE from the left-hand side context that has a matching element in the right-hand side context is [merged][CopyableThreadContextElement.mergeForChild]
 * * Every CTCE from the right-hand side context that hasn't been merged is copied
 * * Everything else is added to the resulting context as is.
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

// Used by withContext when context changes, but dispatcher stays the same
internal actual class UndispatchedCoroutine<in T>actual constructor (
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(if (context[UndispatchedMarker] == null) context + UndispatchedMarker else context, uCont) {

    /*
     * The state is thread-local because this coroutine can be used concurrently.
     * Scenario of usage (withContinuationContext):
     * val state = saveThreadContext(ctx)
     * try {
     *     invokeSmthWithThisCoroutineAsCompletion() // Completion implies that 'afterResume' will be called
     *     // COROUTINE_SUSPENDED is returned
     * } finally {
     *     thisCoroutine().clearThreadContext() // Concurrently the "smth" could've been already resumed on a different thread
     *     // and it also calls saveThreadContext and clearThreadContext
     * }
     */
    private val threadStateToRecover = ThreadLocal<Pair<CoroutineContext, Any?>>()

    /*
     * Indicates that a coroutine has a thread local elements associated with it
     * and that 'threadStateToRecover'.
     * Better than nullable thread-local for easier debugging.
     *
     * It is used as a performance optimization to avoid 'threadStateToRecover' and
     * is prone to false-positives as it is never reset: otherwise
     * it may lead to logical data races between suspensions point where
     * coroutine is yet being suspended in one thread while already being resumed
     * in another.
     */
    @Volatile
    private var threadLocalIsSet = false

    init {
        /*
         * This is a hack for a very specific case in #2930 unless #3253 is implemented.
         * 'ThreadLocalStressTest' covers this change properly.
         *
         * The scenario this change covers is the following:
         * 1) The coroutine is being started as plain non kotlinx.coroutines related suspend function,
         *    e.g. `suspend fun main` or, more importantly, Ktor `SuspendFunGun`, that is invoking
         *    `withContext(tlElement)` which creates `UndispatchedCoroutine`.
         * 2) It (original continuation) is then not wrapped into `DispatchedContinuation` via `intercept()`
         *    and goes neither through `DC.run` nor through `resumeUndispatchedWith` that both
         *    do thread context element tracking.
         * 3) So thread locals never got chance to get properly set up via `saveThreadContext`,
         *    but when `withContext` finishes, it attempts to recover thread locals in its `afterResume`.
         *
         * Here we detect precisely this situation and properly setup context to recover later.
         *
         */
        if (uCont.context[ContinuationInterceptor] !is CoroutineDispatcher) {
            /*
             * We cannot just "read" the elements as there is no such API,
             * so we update-restore it immediately and use the intermediate value
             * as the initial state, leveraging the fact that thread context element
             * is idempotent and such situations are increasingly rare.
             */
            val values = updateThreadContext(context, null)
            restoreThreadContext(context, values)
            saveThreadContext(context, values)
        }
    }

    fun saveThreadContext(context: CoroutineContext, oldValue: Any?) {
        threadLocalIsSet = true // Specify that thread-local is touched at all
        threadStateToRecover.set(context to oldValue)
    }

    fun clearThreadContext(): Boolean {
        if (threadLocalIsSet && threadStateToRecover.get() == null) {
            threadStateToRecover.remove()
            return false
        }
        threadStateToRecover.remove()
        return true
    }

    override fun afterResume(state: Any?) {
        if (threadLocalIsSet) {
            threadStateToRecover.get()?.let { (ctx, value) ->
                restoreThreadContext(ctx, value)
            }
            threadStateToRecover.remove()
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
