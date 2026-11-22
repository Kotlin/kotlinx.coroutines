package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.CoroutineStackFrame

/**
 * Creates a context for a new coroutine.
 *
 * See the documentation of this function's common-code implementation for a general overview.
 * Here, the JVM-specific details are described.
 *
 * - If the [debug mode][DEBUG_PROPERTY_NAME] is enabled,
 *   [newCoroutineContext] assigns a unique identifier to every coroutine for tracking it.
 *   The ID is visible in [toString] of the coroutine context or its job and in the thread name,
 *   as well as in the dumps produced by the `kotlinx-coroutines-debug` module.
 * - [CopyableThreadContextElement] values are combined.
 *   If both the parent and [context] have the same [CopyableThreadContextElement]
 *   (when their [key][CoroutineContext.Key] is equal),
 *   the values are [merged][CopyableThreadContextElement.mergeForChild].
 *   If only the parent or only the [context] has the [CopyableThreadContextElement],
 *   the value is [copied][CopyableThreadContextElement.copyForChild].
 */
@ExperimentalCoroutinesApi
public actual fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = foldCopies(coroutineContext, context)
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
    // Similar to foldCopies, but because no new coroutine is launched, CTCEs existing only in the original context do
    // not need to be copied. The added context is folded into the original like the default implementation of
    // CoroutineContext.plus.
    return addedContext.fold(this) { result, element ->
        if (element !is CopyableThreadContextElement<*>) return@fold result + element // not CTCE, append normally
        val oldElement = result[element.key] ?: return@fold result + element.copyForChild() // new CTCE, append copy
        // otherwise, overwrite oldElement with merged CTCE
        result.replace(element.key, (oldElement as CopyableThreadContextElement<*>).mergeForChild(element))
    }
}

private fun CoroutineContext.hasCopyableElements(): Boolean = when (this) {
    // Fast-path: avoid calling fold for single element contexts, which is the most common case for the added context.
    is CopyableThreadContextElement<*> -> true
    is CoroutineContext.Element -> false
    else -> fold(false) { result, it -> result || it is CopyableThreadContextElement<*> }
}

/**
 * Folds two contexts properly applying [CopyableThreadContextElement] rules when creating a new coroutine.
 *
 * The rules are as follows:
 * - If both contexts have the same (by key) CTCE, they are [merged][CopyableThreadContextElement.mergeForChild].
 * - The CTCEs that one context has and the other does not are [copied][CopyableThreadContextElement.copyForChild].
 * - Every non-CTCE is added to the resulting context as is.
 */
private fun foldCopies(originalContext: CoroutineContext, appendContext: CoroutineContext): CoroutineContext {
    // Fast-path: we can use a simpler fold pass over originalContext to copy CTCEs if appendContext does not contain
    // CTCEs. appendContext being empty is the most common case for new coroutines, so we check that explicitly first.
    if (appendContext === EmptyCoroutineContext || !appendContext.hasCopyableElements()) {
        // Fold originalContext into itself, overwriting CTCEs with copies while leaving other elements alone.
        return originalContext.fold(originalContext) { result, element ->
            if (element !is CopyableThreadContextElement<*>) return@fold result // not CTCE, leave it alone
            result.replace(element.key, element.copyForChild()) // CTCE, overwrite with copy
            // no merging necessary because no CTCEs in appendContext
        } + appendContext // so just append all of it normally
    }

    // Slow-path: appendContext contains one or more CTCEs. We'll need two fold passes over both originalContext and
    // appendContext to merge CTCEs found in both contexts, copy CTCEs found in one context but not the other, and
    // append any remaining elements in appendContext to originalContext.
    var leftoverContext = appendContext
    // Fold originalContext into itself, overwriting CTCEs with copies or merges while leaving other elements alone.
    val folded = originalContext.fold(originalContext) { result, element ->
        if (element !is CopyableThreadContextElement<*>) return@fold result // not CTCE, leave it alone
        val newElement = leftoverContext[element.key]
        if (newElement == null) {
            // no matching CTCE in appendContext
            result.replace(element.key, element.copyForChild()) // overwrite with copy
        } else {
            // found matching CTCE in appendContext
            leftoverContext = leftoverContext.minusKey(element.key) // remove matching element from appendContext
            result.replace(element.key, element.mergeForChild(newElement)) // then overwrite element with merged CTCE
        }
    }
    // Fold remaining elements in leftoverContext into the folded originalContext. Any remaining CTCEs are new and must
    // be copied; non-CTCE elements are appended normally.
    return leftoverContext.fold(folded) { result, element ->
        if (element !is CopyableThreadContextElement<*>) return@fold result + element // not CTCE, append normally
        result + element.copyForChild() // new CTCE, append copy
    }
}

private fun CoroutineContext.replace(key: CoroutineContext.Key<*>, replacement: CoroutineContext): CoroutineContext =
    if (replacement[key] != null) this + replacement else minusKey(key) + replacement

/**
 * Executes a block using a given coroutine context.
 */
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T {
    val oldValue = updateThreadContext(context, countOrElement)
    try {
        return block()
    } finally {
        restoreThreadContext(context, oldValue, countOrElement)
    }
}

/**
 * Executes a block using a context of a given continuation.
 */
internal actual inline fun <T> withContinuationContext(continuation: Continuation<*>, countOrElement: Any?, block: () -> T): T {
    val context = continuation.context
    val oldValue = updateThreadContext(context, countOrElement)
    val threadStateFrame = if (oldValue !== NO_THREAD_ELEMENTS) {
        // Only if some values were replaced we'll go to the slow path of figuring out where/how to restore them
        continuation.updateUndispatchedCompletion(context, oldValue)
    } else {
        null // fast path -- don't even try to find undispatchedCompletion as there's nothing to restore in the context
    }
    try {
        return block()
    } finally {
        if (threadStateFrame == null || threadStateFrame.pop()) {
            restoreThreadContext(context, oldValue, countOrElement)
        }
    }
}

private val threadStateFrames = ThreadLocal<ThreadStateFrame?>()

/**
 * Protocol for storing frames (i.e. thread context state) for a thread in a specific point in time. Frames never
 * leave their thread, avoiding any synchronization on suspend/resume.
 *
 * [withContinuationContext] pushes a frame, the holder consumes it and for the pusher restoration is skipped if
 * frame is consumed
 */
internal class ThreadStateFrame(
    @JvmField val completion: UndispatchedCompletion,
    @JvmField val context: CoroutineContext,
    @JvmField val oldValue: Any?,
    @JvmField val previous: ThreadStateFrame?
) {
    @JvmField var consumed = false

    fun pop(): Boolean {
        // set is used without remove() for performance reasons, it only updates a single field. Calling
        // remove() means having to build an entire entry on every resume. When outermost withContinuationContext
        // finishes, previous is `null` which means between resumes the entry exists but holds nothing,
        // guaranteeing one map entry per thread.
        threadStateFrames.set(previous)
        return !consumed
    }
}

@IgnorableReturnValue
private fun UndispatchedCompletion.restoreSavedThreadContext(): Boolean {
    if (!hasThreadStateFrames) return false
    var frame = threadStateFrames.get()
    while (frame != null) {
        if (frame.completion === this) {
            if (frame.consumed) return false
            frame.consumed = true
            restoreThreadContext(frame.context, frame.oldValue)
            return true
        }
        frame = frame.previous
    }
    return false
}

internal fun Continuation<*>.updateUndispatchedCompletion(context: CoroutineContext, oldValue: Any?): ThreadStateFrame? {
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
    val completion = undispatchedCompletion() ?: return null
    completion.hasThreadStateFrames = true
    // Without this, the recorded state from construction could be restored later on top of a normal thread handoff
    if (completion is UndispatchedCoroutine<*>) completion.discardInitialThreadState()
    return ThreadStateFrame(completion, context, oldValue, threadStateFrames.get()).also { threadStateFrames.set(it) }
}

internal tailrec fun CoroutineStackFrame.undispatchedCompletion(): UndispatchedCompletion? {
    // Find direct completion of this continuation
    val completion: CoroutineStackFrame = when (this) {
        is DispatchedCoroutine<*> -> return null
        else -> callerFrame ?: return null // something else -- not supported
    }
    if (completion is UndispatchedCompletion) return completion
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

private fun CoroutineContext.withUndispatchedMarker(): CoroutineContext =
    if (this[UndispatchedMarker] == null) this + UndispatchedMarker else this

// A marker is needed when a key gets added which the caller lacks in order for resumption to hand-off correctly.
// Without it, you would have nesting (which is correct only when no key is added)
internal actual fun CoroutineContext.withUndispatchedMarkerIfNeeded(callerContext: CoroutineContext): CoroutineContext {
    if (this[UndispatchedMarker] != null) return this
    val hasElementsAbsentInCaller = fold(false) { found, element ->
        found || element is ThreadContextElement<*> && callerContext[element.key] == null
    }
    return if (hasElementsAbsentInCaller) this + UndispatchedMarker else this
}

internal sealed interface UndispatchedCompletion {
    // Since frames never leave a physical Thread, a plain var here is enough. @Volatile is not needed since
    // the only Thread that needs to see true is the same one that pushed the frame. The value is also never set
    // to false, so there isn't a case of another thread needing to see this state change.
    var hasThreadStateFrames: Boolean
}

// Used by withContext when context changes, but dispatcher stays the same. See ThreadStateFrame for the protocol.
internal actual class UndispatchedCoroutine<in T>actual constructor (
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context.withUndispatchedMarker(), uCont), UndispatchedCompletion {

    override var hasThreadStateFrames = false

    private var initialThreadState: InitialThreadState? = null

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
         * 3) As a result, no frame gets pushed for this coroutine (which would ordinarily happen in
         *    `updateUndispatchedCompletion` called within a `withContinuationContext`).
         * 4) Recovery then happens in `restoreThreadState()` which `afterResume`/`afterCompletionUndispatched` call.
         *    So `restoreThreadState()` doesn't find a frame and hence nothing ends up being restored which is what
         *    causes the values within the `ThreadLocal` to leak.
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
            initialThreadState = InitialThreadState(Thread.currentThread(), context, values)
        }
    }

    fun discardInitialThreadState() {
        val state = initialThreadState ?: return
        if (state.thread === Thread.currentThread()) initialThreadState = null
    }

    override fun afterCompletionUndispatched() {
        restoreThreadState()
    }

    override fun afterResume(state: Any?) {
        restoreThreadState()
        // resume undispatched -- update context but stay on the same dispatcher
        val result = recoverResult(state, uCont)
        withContinuationContext(uCont, null) {
            uCont.resumeWith(result)
        }
    }

    private fun restoreThreadState() {
        val restored = restoreSavedThreadContext()
        val state = initialThreadState ?: return
        if (state.thread !== Thread.currentThread()) return
        initialThreadState = null
        if (!restored) restoreThreadContext(state.context, state.oldValue)
    }

    private class InitialThreadState(
        @JvmField val thread: Thread,
        @JvmField val context: CoroutineContext,
        @JvmField val oldValue: Any?
    )
}

internal actual class StackFrameContinuation<T> actual constructor(
    private val uCont: Continuation<T>,
    override val context: CoroutineContext,
    private val callerContext: CoroutineContext?,
    private val callerCountOrElement: Any?
) : Continuation<T>, CoroutineStackFrame, UndispatchedCompletion {

    override var hasThreadStateFrames = false

    override val callerFrame: CoroutineStackFrame?
        get() = uCont as? CoroutineStackFrame

    // Only runs when inner block finishes after a suspension
    override fun resumeWith(result: Result<T>) {
        restoreSavedThreadContext()
        // === is intentional, it's only valid from the exact object reference it was computed from.
        // == would introduce an expensive check that is being avoided.
        val countOrElement = if (uCont.context === callerContext) callerCountOrElement else null
        withContinuationContext(uCont, countOrElement) {
            uCont.resumeWith(result)
        }
    }

    override fun getStackTraceElement(): StackTraceElement? = null
}

internal actual val CoroutineContext.coroutineName: String? get() {
    if (!DEBUG) return null
    val coroutineId = this[CoroutineId] ?: return null
    val coroutineName = this[CoroutineName]?.name ?: "coroutine"
    return "$coroutineName#${coroutineId.id}"
}

private const val DEBUG_THREAD_NAME_SEPARATOR = " @"

@IgnoreJreRequirement // desugared hashcode implementation
@PublishedApi
internal data class CoroutineId(
    // Used by the IDEA debugger via reflection and must be kept binary-compatible, see KTIJ-24102
    val id: Long
) : ThreadContextElement<String>, AbstractCoroutineContextElement(CoroutineId) {
    // Used by the IDEA debugger via reflection and must be kept binary-compatible, see KTIJ-24102
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
