@file:JvmMultifileClass
@file:JvmName("BuildersKt")
@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlin.concurrent.Volatile
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*

// --------------- launch ---------------

/**
 * Launches a new coroutine without blocking the current thread and returns a reference to the coroutine as a [Job].
 * The coroutine is cancelled when the resulting job is [cancelled][Job.cancel].
 *
 * The coroutine context is inherited from a [CoroutineScope]. Additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with a corresponding [context] element.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other start options can be specified via `start` parameter. See [CoroutineStart] for details.
 * An optional [start] parameter can be set to [CoroutineStart.LAZY] to start coroutine _lazily_. In this case,
 * the coroutine [Job] is created in _new_ state. It can be explicitly started with [start][Job.start] function
 * and will be started implicitly on the first invocation of [join][Job.join].
 *
 * Uncaught exceptions in this coroutine cancel the parent job in the context by default
 * (unless [CoroutineExceptionHandler] is explicitly specified), which means that when `launch` is used with
 * the context of another coroutine, then any uncaught exception leads to the cancellation of the parent coroutine.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for a newly created coroutine.
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param block the coroutine code which will be invoked in the context of the provided scope.
 **/
public fun CoroutineScope.launch(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> Unit
): Job {
    val newContext = newCoroutineContext(context)
    val coroutine = if (start.isLazy)
        LazyStandaloneCoroutine(newContext, block) else
        StandaloneCoroutine(newContext, active = true)
    coroutine.start(start, coroutine, block)
    return coroutine
}

// --------------- async ---------------

/**
 * Creates a coroutine and returns its future result as an implementation of [Deferred].
 * The running coroutine is cancelled when the resulting deferred is [cancelled][Job.cancel].
 * The resulting coroutine has a key difference compared with similar primitives in other languages
 * and frameworks: it cancels the parent job (or outer scope) on failure to enforce *structured concurrency* paradigm.
 * To change that behaviour, supervising parent ([SupervisorJob] or [supervisorScope]) can be used.
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [context] element.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * An optional [start] parameter can be set to [CoroutineStart.LAZY] to start coroutine _lazily_. In this case,
 * the resulting [Deferred] is created in _new_ state. It can be explicitly started with [start][Job.start]
 * function and will be started implicitly on the first invocation of [join][Job.join], [await][Deferred.await] or [awaitAll].
 *
 * @param block the coroutine code.
 */
public fun <T> CoroutineScope.async(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): Deferred<T> {
    val newContext = newCoroutineContext(context)
    val coroutine = if (start.isLazy)
        LazyDeferredCoroutine(newContext, block) else
        DeferredCoroutine<T>(newContext, active = true)
    coroutine.start(start, coroutine, block)
    return coroutine
}

@OptIn(InternalForInheritanceCoroutinesApi::class)
@Suppress("UNCHECKED_CAST")
private open class DeferredCoroutine<T>(
    parentContext: CoroutineContext,
    active: Boolean
) : AbstractCoroutine<T>(parentContext, true, active = active), Deferred<T> {
    override fun getCompleted(): T = getCompletedInternal() as T
    override suspend fun await(): T = awaitInternal() as T
    override val onAwait: SelectClause1<T> get() = onAwaitInternal as SelectClause1<T>
}

private class LazyDeferredCoroutine<T>(
    parentContext: CoroutineContext,
    block: suspend CoroutineScope.() -> T
) : DeferredCoroutine<T>(parentContext, active = false) {
    private val continuation = block.createCoroutineUnintercepted(this, this)

    override fun onStart() {
        continuation.startCoroutineCancellable(this)
    }
}

// --------------- withContext ---------------

/**
 * Calls the specified suspending block with a given coroutine context, suspends until it completes, and returns
 * the result.
 *
 * The resulting context for the [block] is derived by merging the current [coroutineContext] with the
 * specified [context] using `coroutineContext + context` (see [CoroutineContext.plus]).
 * This suspending function is cancellable. It immediately checks for cancellation of
 * the resulting context and throws [CancellationException] if it is not [active][CoroutineContext.isActive].
 *
 * Calls to [withContext] whose [context] argument provides a [CoroutineDispatcher] that is
 * different from the current one, by necessity, perform additional dispatches: the [block]
 * can not be executed immediately and needs to be dispatched for execution on
 * the passed [CoroutineDispatcher], and then when the [block] completes, the execution
 * has to shift back to the original dispatcher.
 *
 * Note that the result of `withContext` invocation is dispatched into the original context in a cancellable way
 * with a **prompt cancellation guarantee**, which means that if the original [coroutineContext]
 * in which `withContext` was invoked is cancelled by the time its dispatcher starts to execute the code,
 * it discards the result of `withContext` and throws [CancellationException].
 *
 * The cancellation behaviour described above is enabled if and only if the dispatcher is being changed.
 * For example, when using `withContext(NonCancellable) { ... }` there is no change in dispatcher and
 * this call will not be cancelled neither on entry to the block inside `withContext` nor on exit from it.
 */
public suspend fun <T> withContext(
    context: CoroutineContext,
    block: suspend CoroutineScope.() -> T
): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return suspendCoroutineUninterceptedOrReturn sc@ { uCont ->
        // compute new context
        val oldContext = uCont.context
        // Copy CopyableThreadContextElement if necessary
        val newContext = oldContext.newCoroutineContext(context)
        // always check for cancellation of new context
        newContext.ensureActive()
        // FAST PATH #1 -- new context is the same as the old one
        if (newContext === oldContext) {
            val coroutine = ScopeCoroutine(newContext, uCont)
            return@sc coroutine.startUndispatchedOrReturn(coroutine, block)
        }
        // FAST PATH #2 -- the new dispatcher is the same as the old one (something else changed)
        // `equals` is used by design (see equals implementation is wrapper context like ExecutorCoroutineDispatcher)
        if (newContext[ContinuationInterceptor] == oldContext[ContinuationInterceptor]) {
            val coroutine = UndispatchedCoroutine(newContext, uCont)
            // There are changes in the context, so this thread needs to be updated
            withCoroutineContext(coroutine.context, null) {
                return@sc coroutine.startUndispatchedOrReturn(coroutine, block)
            }
        }
        // SLOW PATH -- use new dispatcher
        val coroutine = DispatchedCoroutine(newContext, uCont)
        block.startCoroutineCancellable(coroutine, coroutine)
        coroutine.getResult()
    }
}

/**
 * Calls the specified suspending block with the given [CoroutineDispatcher], suspends until it
 * completes, and returns the result.
 *
 * This inline function calls [withContext].
 */
public suspend inline operator fun <T> CoroutineDispatcher.invoke(
    noinline block: suspend CoroutineScope.() -> T
): T = withContext(this, block)

// --------------- implementation ---------------

private open class StandaloneCoroutine(
    parentContext: CoroutineContext,
    active: Boolean
) : AbstractCoroutine<Unit>(parentContext, initParentJob = true, active = active) {
    override fun handleJobException(exception: Throwable): Boolean {
        handleCoroutineException(context, exception)
        return true
    }
}

private class LazyStandaloneCoroutine(
    parentContext: CoroutineContext,
    block: suspend CoroutineScope.() -> Unit
) : StandaloneCoroutine(parentContext, active = false) {
    private val continuation = block.createCoroutineUnintercepted(this, this)

    override fun onStart() {
        continuation.startCoroutineCancellable(this)
    }
}

// Used by withContext when context changes, but dispatcher stays the same
internal class UndispatchedCoroutine<in T>(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(if (context[UndispatchedMarker] == null) context + UndispatchedMarker else context, uCont) {

    /**
     * The state of [ThreadContextElement]s associated with the current undispatched coroutine.
     * It is stored in a thread local because this coroutine can be used concurrently in suspend-resume race scenario.
     * See the followin, boiled down example with inlined `withContinuationContext` body:
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
     * Each access to [CommonThreadLocal] on JVM leaves a footprint in the corresponding Thread's `ThreadLocalMap`
     * that is cleared automatically as soon as the associated thread-local (-> UndispatchedCoroutine) is garbage collected.
     * When such coroutines are promoted to old generation, `ThreadLocalMap`s become bloated and an arbitrary accesses to thread locals
     * start to consume significant amount of CPU because these maps are open-addressed and cleaned up incrementally on each access.
     * (You can read more about this effect as "GC nepotism").
     *
     * To avoid that, we attempt to narrow down the lifetime of this thread local as much as possible:
     * - It's never accessed when we are sure there are no thread context elements
     * - It's cleaned up via [CommonThreadLocal.remove] as soon as the coroutine is suspended or finished.
     */
    private val threadStateToRecover = commonThreadLocal<Pair<CoroutineContext, Any?>?>(Symbol("UndispatchedCoroutine"))

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

private const val UNDECIDED = 0
private const val SUSPENDED = 1
private const val RESUMED = 2

// Used by withContext when context dispatcher changes
internal class DispatchedCoroutine<in T>(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {
    // this is copy-and-paste of a decision state machine inside AbstractionContinuation
    // todo: we may some-how abstract it via inline class
    private val _decision = atomic(UNDECIDED)

    private fun trySuspend(): Boolean {
        _decision.loop { decision ->
            when (decision) {
                UNDECIDED -> if (this._decision.compareAndSet(UNDECIDED, SUSPENDED)) return true
                RESUMED -> return false
                else -> error("Already suspended")
            }
        }
    }

    private fun tryResume(): Boolean {
        _decision.loop { decision ->
            when (decision) {
                UNDECIDED -> if (this._decision.compareAndSet(UNDECIDED, RESUMED)) return true
                SUSPENDED -> return false
                else -> error("Already resumed")
            }
        }
    }

    override fun afterCompletion(state: Any?) {
        // Call afterResume from afterCompletion and not vice-versa, because stack-size is more
        // important for afterResume implementation
        afterResume(state)
    }

    override fun afterResume(state: Any?) {
        if (tryResume()) return // completed before getResult invocation -- bail out
        // Resume in a cancellable way because we have to switch back to the original dispatcher
        uCont.intercepted().resumeCancellableWith(recoverResult(state, uCont))
    }

    internal fun getResult(): Any? {
        if (trySuspend()) return COROUTINE_SUSPENDED
        // otherwise, onCompletionInternal was already invoked & invoked tryResume, and the result is in the state
        val state = this.state.unboxState()
        if (state is CompletedExceptionally) throw state.cause
        @Suppress("UNCHECKED_CAST")
        return state as T
    }
}
