/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
    final override val delegate: Continuation<T>,
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

    private val _parentHandle = atomic<DisposableHandle?>(null)
    private var parentHandle: DisposableHandle?
        get() = _parentHandle.value
        set(value) { _parentHandle.value = value }

    internal val state: Any? get() = _state.value

    public override val isActive: Boolean get() = state is NotCompleted

    public override val isCompleted: Boolean get() = state !is NotCompleted

    public override val isCancelled: Boolean get() = state is CancelledContinuation

    public override fun initCancellability() {
        // This method does nothing. Leftover for binary compatibility with old compiled code
    }

    private fun isReusable(): Boolean = delegate is DispatchedContinuation<*> && delegate.isReusable

    /**
     * Resets cancellability state in order to [suspendAtomicCancellableCoroutineReusable] to work.
     * Invariant: used only by [suspendAtomicCancellableCoroutineReusable] in [REUSABLE_CLAIMED] state.
     */
    internal fun resetState(): Boolean {
        assert { parentHandle !== NonDisposableHandle }
        val state = _state.value
        assert { state !is NotCompleted }
        if (state is CompletedIdempotentResult) {
            detachChild()
            return false
        }
        _decision.value = UNDECIDED
        _state.value = Active
        return true
    }

    /**
     * Setups parent cancellation and checks for postponed cancellation in the case of reusable continuations.
     * It is only invoked from an internal [getResult] function.
     */
    private fun setupCancellation() {
        if (checkCompleted()) return
        if (parentHandle !== null) return // fast path 2 -- was already initialized
        val parent = delegate.context[Job] ?: return // fast path 3 -- don't do anything without parent
        parent.start() // make sure the parent is started
        val handle = parent.invokeOnCompletion(
            onCancelling = true,
            handler = ChildContinuation(parent, this).asHandler
        )
        parentHandle = handle
        // now check our state _after_ registering (could have completed while we were registering)
        // Also note that we do not dispose parent for reusable continuations, dispatcher will do that for us
        if (isCompleted && !isReusable()) {
            handle.dispose() // it is Ok to call dispose twice -- here and in disposeParentHandle
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
    }

    private fun checkCompleted(): Boolean {
        val completed = isCompleted
        if (resumeMode != MODE_ATOMIC_DEFAULT) return completed // Do not check postponed cancellation for non-reusable continuations
        val dispatched = delegate as? DispatchedContinuation<*> ?: return completed
        val cause = dispatched.checkPostponedCancellation(this) ?: return completed
        if (!completed) {
            // Note: this cancel may fail if one more concurrent cancel is currently being invoked
            cancel(cause)
        }
        return true
    }

    public override val callerFrame: CoroutineStackFrame?
        get() = delegate as? CoroutineStackFrame

    public override fun getStackTraceElement(): StackTraceElement? = null

    override fun takeState(): Any? = state

    override fun cancelResult(state: Any?, cause: Throwable) {
        if (state is CompletedWithCancellation) {
            invokeHandlerSafely {
                state.onCancellation(cause)
            }
        }
    }

    /*
     * Attempt to postpone cancellation for reusable cancellable continuation
     */
    private fun cancelLater(cause: Throwable): Boolean {
        if (resumeMode != MODE_ATOMIC_DEFAULT) return false
        val dispatched = (delegate as? DispatchedContinuation<*>) ?: return false
        return dispatched.postponeCancellation(cause)
    }

    public override fun cancel(cause: Throwable?): Boolean {
        _state.loop { state ->
            if (state !is NotCompleted) return false // false if already complete or cancelling
            // Active -- update to final state
            val update = CancelledContinuation(this, cause, handled = state is CancelHandler)
            if (!_state.compareAndSet(state, update)) return@loop // retry on cas failure
            // Invoke cancel handler if it was present
            if (state is CancelHandler) invokeHandlerSafely { state.invoke(cause) }
            // Complete state update
            detachChildIfNonResuable()
            dispatchResume(mode = MODE_ATOMIC_DEFAULT)
            return true
        }
    }

    internal fun parentCancelled(cause: Throwable) {
        if (cancelLater(cause)) return
        cancel(cause)
        // Even if cancellation has failed, we should detach child to avoid potential leak
        detachChildIfNonResuable()
    }

    private inline fun invokeHandlerSafely(block: () -> Unit) {
        try {
            block()
        } catch (ex: Throwable) {
            // Handler should never fail, if it does -- it is an unhandled exception
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
        setupCancellation()
        if (trySuspend()) return COROUTINE_SUSPENDED
        // otherwise, onCompletionInternal was already invoked & invoked tryResume, and the result is in the state
        val state = this.state
        if (state is CompletedExceptionally) throw recoverStackTrace(state.cause, this)
        // if the parent job was already cancelled, then throw the corresponding cancellation exception
        // otherwise, there is a race is suspendCancellableCoroutine { cont -> ... } does cont.resume(...)
        // before the block returns. This getResult would return a result as opposed to cancellation
        // exception that should have happened if the continuation is dispatched for execution later.
        if (resumeMode == MODE_CANCELLABLE) {
            val job = context[Job]
            if (job != null && !job.isActive) {
                val cause = job.getCancellationException()
                cancelResult(state, cause)
                throw recoverStackTrace(cause, this)
            }
        }
        return getSuccessfulResult(state)
    }

    override fun resumeWith(result: Result<T>) {
        resumeImpl(result.toState(), resumeMode)
    }

    override fun resume(value: T, onCancellation: (cause: Throwable) -> Unit) {
        val cancelled = resumeImpl(CompletedWithCancellation(value, onCancellation), resumeMode)
        if (cancelled != null) {
            // too late to resume (was cancelled) -- call handler
            invokeHandlerSafely {
                onCancellation(cancelled.cause)
            }
        }
    }

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
                is CancelHandler -> multipleHandlersError(handler, state)
                is CancelledContinuation -> {
                    /*
                     * Continuation was already cancelled, invoke directly.
                     * NOTE: multiple invokeOnCancellation calls with different handlers are not allowed,
                     * so we check to make sure that handler was installed just once.
                     */
                    if (!state.makeHandled()) multipleHandlersError(handler, state)
                    /*
                     * :KLUDGE: We have to invoke a handler in platform-specific way via `invokeIt` extension,
                     * because we play type tricks on Kotlin/JS and handler is not necessarily a function there
                     */
                    invokeHandlerSafely { handler.invokeIt((state as? CompletedExceptionally)?.cause) }
                    return
                }
                else -> {
                    /*
                     * Continuation was already completed, do nothing.
                     * NOTE: multiple invokeOnCancellation calls with different handlers are not allowed,
                     * but we have no way to check that it was installed just once in this case.
                     */
                    return
                }
            }
        }
    }

    private fun multipleHandlersError(handler: CompletionHandler, state: Any?) {
        error("It's prohibited to register multiple handlers, tried to register $handler, already has $state")
    }

    private fun makeHandler(handler: CompletionHandler): CancelHandler =
        if (handler is CancelHandler) handler else InvokeOnCancel(handler)

    private fun dispatchResume(mode: Int) {
        if (tryResume()) return // completed before getResult invocation -- bail out
        // otherwise, getResult has already commenced, i.e. completed later or in other thread
        dispatch(mode)
    }

    // returns null when successfully dispatched resumed, CancelledContinuation if too late (was already cancelled)
    private fun resumeImpl(proposedUpdate: Any?, resumeMode: Int): CancelledContinuation? {
        _state.loop { state ->
            when (state) {
                is NotCompleted -> {
                    if (!_state.compareAndSet(state, proposedUpdate)) return@loop // retry on cas failure
                    detachChildIfNonResuable()
                    dispatchResume(resumeMode)
                    return null
                }
                is CancelledContinuation -> {
                    /*
                     * If continuation was cancelled, then resume attempt must be ignored,
                     * because cancellation is asynchronous and may race with resume.
                     * Racy exceptions will be lost, too.
                     */
                    if (state.makeResumed()) return state // tried to resume just once, but was cancelled
                }
            }
            alreadyResumedError(proposedUpdate) // otherwise -- an error (second resume attempt)
        }
    }

    private fun alreadyResumedError(proposedUpdate: Any?) {
        error("Already resumed, but proposed with update $proposedUpdate")
    }

    // Unregister from parent job
    private fun detachChildIfNonResuable() {
        // If instance is reusable, do not detach on every reuse, #releaseInterceptedContinuation will do it for us in the end
        if (!isReusable()) detachChild()
    }

    /**
     * Detaches from the parent.
     * Invariant: used used from [CoroutineDispatcher.releaseInterceptedContinuation] iff [isReusable] is `true`
     */
    internal fun detachChild() {
        val handle = parentHandle
        handle?.dispose()
        parentHandle = NonDisposableHandle
    }

    override fun tryResume(value: T, idempotent: Any?): Any? {
        _state.loop { state ->
            when (state) {
                is NotCompleted -> {
                    val update: Any? = if (idempotent == null) value else
                        CompletedIdempotentResult(idempotent, value, state)
                    if (!_state.compareAndSet(state, update)) return@loop // retry on cas failure
                    detachChildIfNonResuable()
                    return state
                }
                is CompletedIdempotentResult -> {
                    return if (state.idempotentResume === idempotent) {
                        assert { state.result === value } // "Non-idempotent resume"
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
                    detachChildIfNonResuable()
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
        when (state) {
            is CompletedIdempotentResult -> state.result as T
            is CompletedWithCancellation -> state.result as T
            else -> state as T
        }

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

private class CompletedWithCancellation(
    @JvmField val result: Any?,
    @JvmField val onCancellation: (cause: Throwable) -> Unit
) {
    override fun toString(): String = "CompletedWithCancellation[$result]"
}

