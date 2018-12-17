/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*

private const val UNDECIDED = 0
private const val SUSPENDED = 1
private const val RESUMED = 2

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
@PublishedApi
internal open class CancellableContinuationImpl<in T>(
    public final override val delegate: Continuation<T>,
    resumeMode: Int
) : DispatchedTask<T>(resumeMode), CancellableContinuation<T>, CoroutineStackFrame {
    public override val context: CoroutineContext = delegate.context

    /*
     * Implementation notes
     *
     * AbstractContinuation is a subset of Job with following limitations:
     * 1) It can have only cancellation listeners
     * 2) It always invokes cancellation listener if it's cancelled (no 'invokeImmediately')
     * 3) It can have at most one cancellation listener
     * 4) Its cancellation listeners cannot be deregistered
     * As a consequence it has much simpler state machine, more lightweight machinery and
     * less dependencies.
     */

    /* decision state machine

        +-----------+   trySuspend   +-----------+
        | UNDECIDED | -------------> | SUSPENDED |
        +-----------+                +-----------+
              |
              | tryResume
              V
        +-----------+
        |  RESUMED  |
        +-----------+

        Note: both tryResume and trySuspend can be invoked at most once, first invocation wins
     */
    private val _decision = atomic(UNDECIDED)

    /*
       === Internal states ===
       name        state class          public state    description
       ------      ------------         ------------    -----------
       ACTIVE      Active               : Active        active, no listeners
       SINGLE_A    CancelHandler        : Active        active, one cancellation listener
       CANCELLED   CancelledContinuation: Cancelled     cancelled (final state)
       COMPLETED   any                  : Completed     produced some result or threw an exception (final state)
     */
    private val _state = atomic<Any?>(Active)

    @Volatile
    private var parentHandle: DisposableHandle? = null

    internal val state: Any? get() = _state.value

    public override val isActive: Boolean get() = state is NotCompleted

    public override val isCompleted: Boolean get() = state !is NotCompleted

    public override val isCancelled: Boolean get() = state is CancelledContinuation

    public override fun initCancellability() {
        // This method does nothing. Leftover for binary compatibility with old compiled code
    }

    // It is only invoked from an internal getResult function, so we can be sure it is not invoked twice
    private fun installParentCancellationHandler() {
        if (isCompleted) return // fast path 1 -- don't need to do anything if already completed
        val parent = delegate.context[Job] ?: return // fast path 2 -- don't do anything without parent
        parent.start() // make sure the parent is started
        val handle = parent.invokeOnCompletion(
            onCancelling = true,
            handler = ChildContinuation(parent, this).asHandler
        )
        parentHandle = handle
        // now check our state _after_ registering (could have completed while we were registering)
        if (isCompleted) {
            handle.dispose() // it is Ok to call dispose twice -- here and in disposeParentHandle
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
    }

    public override val callerFrame: CoroutineStackFrame?
        get() = delegate as? CoroutineStackFrame

    public override fun getStackTraceElement(): StackTraceElement? = null

    override fun takeState(): Any? = state

    public override fun cancel(cause: Throwable?): Boolean {
        _state.loop { state ->
            if (state !is NotCompleted) return false // false if already complete or cancelling
            // Active -- update to final state
            if (!_state.compareAndSet(state, CancelledContinuation(this, cause))) return@loop // retry on cas failure
            // Invoke cancel handler if it was present
            if (state is CancelHandler) invokeHandlerSafely { state.invoke(cause) }
            // Complete state update
            disposeParentHandle()
            dispatchResume(mode = MODE_ATOMIC_DEFAULT)
            return true
        }
    }

    private inline fun invokeHandlerSafely(block: () -> Unit) {
        try {
            block()
        } catch (ex: Throwable) {
            handleCoroutineException(
                context,
                CompletionHandlerException("Exception in cancellation handler for $this", ex)
            )
        }
    }

    /**
     * It is used when parent is cancelled to get the cancellation cause for this continuation.
     */
    open fun getContinuationCancellationCause(parent: Job): Throwable =
        parent.getCancellationException()

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

    @PublishedApi
    internal fun getResult(): Any? {
        installParentCancellationHandler()
        if (trySuspend()) return COROUTINE_SUSPENDED
        // otherwise, onCompletionInternal was already invoked & invoked tryResume, and the result is in the state
        val state = this.state
        if (state is CompletedExceptionally) throw recoverStackTrace(state.cause, this)
        return getSuccessfulResult(state)
    }

    override fun resumeWith(result: Result<T>) =
        resumeImpl(result.toState(), resumeMode)

    internal fun resumeWithExceptionMode(exception: Throwable, mode: Int) =
        resumeImpl(CompletedExceptionally(exception), mode)

    public override fun invokeOnCancellation(handler: CompletionHandler) {
        var handleCache: CancelHandler? = null
        _state.loop { state ->
            when (state) {
                is Active -> {
                    val node = handleCache ?: makeHandler(handler).also { handleCache = it }
                    if (_state.compareAndSet(state, node)) return // quit on cas success
                }
                is CancelHandler -> {
                    error("It's prohibited to register multiple handlers, tried to register $handler, already has $state")
                }
                is CancelledContinuation -> {
                    /*
                     * Continuation was already cancelled, invoke directly.
                     * NOTE: multiple invokeOnCancellation calls with different handlers are allowed on cancelled continuation.
                     * It's inconsistent with running continuation, but currently, we have no mechanism to check
                     * whether any handler was registered during continuation lifecycle without additional overhead.
                     * This may be changed in the future.
                     *
                     * :KLUDGE: We have to invoke a handler in platform-specific way via `invokeIt` extension,
                     * because we play type tricks on Kotlin/JS and handler is not necessarily a function there
                     */
                    invokeHandlerSafely { handler.invokeIt((state as? CompletedExceptionally)?.cause) }
                    return
                }
                else -> return
            }
        }
    }

    private fun makeHandler(handler: CompletionHandler): CancelHandler =
        if (handler is CancelHandler) handler else InvokeOnCancel(handler)

    private fun dispatchResume(mode: Int) {
        if (tryResume()) return // completed before getResult invocation -- bail out
        // otherwise, getResult has already commenced, i.e. completed later or in other thread
        dispatch(mode)
    }

    private fun resumeImpl(proposedUpdate: Any?, resumeMode: Int) {
        _state.loop { state ->
            when (state) {
                is NotCompleted -> {
                    if (!_state.compareAndSet(state, proposedUpdate)) return@loop // retry on cas failure
                    disposeParentHandle()
                    dispatchResume(resumeMode)
                    return
                }
                is CancelledContinuation -> {
                    /*
                     * If continuation was cancelled, then all further resumes must be
                     * ignored, because cancellation is asynchronous and may race with resume.
                     * Racy exceptions will be lost, too. There does not see to be a safe way to
                     * handle them without producing spurious crashes.
                     *
                     * :todo: we should somehow remember the attempt to invoke resume and fail on the second attempt.
                     */
                    return
                }
                else -> error("Already resumed, but proposed with update $proposedUpdate")
            }
        }
    }

    // Unregister from parent job
    private fun disposeParentHandle() {
        parentHandle?.let { // volatile read parentHandle (once)
            it.dispose()
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
    }

    override fun tryResume(value: T, idempotent: Any?): Any? {
        _state.loop { state ->
            when (state) {
                is NotCompleted -> {
                    val update: Any? = if (idempotent == null) value else
                        CompletedIdempotentResult(idempotent, value, state)
                    if (!_state.compareAndSet(state, update)) return@loop // retry on cas failure
                    disposeParentHandle()
                    return state
                }
                is CompletedIdempotentResult -> {
                    return if (state.idempotentResume === idempotent) {
                        check(state.result === value) { "Non-idempotent resume" }
                        state.token
                    } else {
                        null
                    }
                }
                else -> return null // cannot resume -- not active anymore
            }
        }
    }

    override fun tryResumeWithException(exception: Throwable): Any? {
        _state.loop { state ->
            when (state) {
                is NotCompleted -> {
                    val update = CompletedExceptionally(exception)
                    if (!_state.compareAndSet(state, update)) return@loop // retry on cas failure
                    disposeParentHandle()
                    return state
                }
                else -> return null // cannot resume -- not active anymore
            }
        }
    }

    override fun completeResume(token: Any) {
        // note: We don't actually use token anymore, because handler needs to be invoked on cancellation only
        dispatchResume(resumeMode)
    }

    override fun CoroutineDispatcher.resumeUndispatched(value: T) {
        val dc = delegate as? DispatchedContinuation
        resumeImpl(value, if (dc?.dispatcher === this) MODE_UNDISPATCHED else resumeMode)
    }

    override fun CoroutineDispatcher.resumeUndispatchedWithException(exception: Throwable) {
        val dc = delegate as? DispatchedContinuation
        resumeImpl(CompletedExceptionally(exception), if (dc?.dispatcher === this) MODE_UNDISPATCHED else resumeMode)
    }

    @Suppress("UNCHECKED_CAST")
    override fun <T> getSuccessfulResult(state: Any?): T =
        if (state is CompletedIdempotentResult) state.result as T else state as T

    // For nicer debugging
    public override fun toString(): String =
        "${nameString()}(${delegate.toDebugString()}){$state}@$hexAddress"

    protected open fun nameString(): String =
        "CancellableContinuation"

}

// Marker for active continuation
internal interface NotCompleted

private object Active : NotCompleted {
    override fun toString(): String = "Active"
}

internal abstract class CancelHandler : CancelHandlerBase(), NotCompleted

// Wrapper for lambdas, for the performance sake CancelHandler can be subclassed directly
private class InvokeOnCancel( // Clashes with InvokeOnCancellation
    private val handler: CompletionHandler
) : CancelHandler() {
    override fun invoke(cause: Throwable?) {
        handler.invoke(cause)
    }
    override fun toString() = "InvokeOnCancel[${handler.classSimpleName}@$hexAddress]"
}

private class CompletedIdempotentResult(
    @JvmField val idempotentResume: Any?,
    @JvmField val result: Any?,
    @JvmField val token: NotCompleted
) {
    override fun toString(): String = "CompletedIdempotentResult[$result]"
}
