package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.concurrent.*
import kotlin.coroutines.*
import kotlin.native.concurrent.ThreadLocal
import kotlin.native.ref.*

internal actual object DefaultExecutor : CoroutineDispatcher(), Delay {

    private val delegate = WorkerDispatcher(name = "DefaultExecutor")

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        delegate.dispatch(context, block)
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        delegate.scheduleResumeAfterDelay(timeMillis, continuation)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        return delegate.invokeOnTimeout(timeMillis, block, context)
    }

    actual fun enqueue(task: Runnable): Unit {
        delegate.dispatch(EmptyCoroutineContext, task)
    }
}

internal expect fun createDefaultDispatcher(): CoroutineDispatcher

@PublishedApi
internal actual val DefaultDelay: Delay = DefaultExecutor

public actual fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = coroutineContext + context
    return if (combined !== Dispatchers.Default && combined[ContinuationInterceptor] == null)
        combined + Dispatchers.Default else combined
}

public actual fun CoroutineContext.newCoroutineContext(addedContext: CoroutineContext): CoroutineContext {
    return this + addedContext
}

// No debugging facilities on native
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
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on native

internal actual class UndispatchedCoroutine<in T>actual constructor (
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(if (context[UndispatchedMarker] == null) context + UndispatchedMarker else context, uCont) {

    /**
     * The state of [ThreadContextElement]s associated with the current undispatched coroutine.
     * It is stored in a thread local because this coroutine can be used concurrently in suspend-resume race scenario.
     * See the following, boiled down example with inlined `withContinuationContext` body:
     * ```
     * val state = saveThreadContext(ctx)
     * try {
     *     invokeSmthWithThisCoroutineAsCompletion() // Completion implies that 'afterResume' will be called
     *     // COROUTINE_SUSPENDED is returned
     * } finally {
     *     thisCoroutine().clearThreadContext() // Concurrently the "smth" could've been already resumed on a different thread
     *     // and it also calls saveThreadContext and clearThreadContext
     * }
     * ```
     *
     * Usage note:
     *
     * This part of the code is performance-sensitive.
     * It is a well-established pattern to wrap various activities into system-specific undispatched
     * `withContext` for the sake of logging, MDC, tracing etc., meaning that there exists thousands of
     * undispatched coroutines.
     * [ThreadLocal.set] leaves a footprint in the corresponding Thread's `ThreadLocalMap`.
     * We attempt to narrow down the lifetime of this thread local as much as possible:
     * - It's never accessed when we are sure there are no thread context elements
     * - It's cleaned up via [ThreadLocal.remove] as soon as the coroutine is suspended or finished.
     */
    private val threadStateToRecover = ThreadLocal<Pair<CoroutineContext, Any?>?>(this)

    /*
     * Indicates that a coroutine has at least one thread context element associated with it
     * and that 'threadStateToRecover' is going to be set in case of dispatchhing in order to preserve them.
     * Better than nullable thread-local for easier debugging.
     *
     * It is used as a performance optimization to avoid 'threadStateToRecover' initialization
     * (note: tl.get() initializes thread local),
     * and is prone to false-positives as it is never reset: otherwise
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
        return !(threadLocalIsSet && threadStateToRecover.get() == null).also {
            threadStateToRecover.remove()
        }
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

private class ThreadLocal<T>(private val key: Any) {
    @Suppress("UNCHECKED_CAST")
    fun get(): T? = ThreadLocalMap[key] as? T
    fun set(value: T) { ThreadLocalMap[key] = value }
    fun remove() { ThreadLocalMap.remove(key) }
}

@ThreadLocal
private object ThreadLocalMap: MutableMap<Any, Any?> by mutableMapOf()
