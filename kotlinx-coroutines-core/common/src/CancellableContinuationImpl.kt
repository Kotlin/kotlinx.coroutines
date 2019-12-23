/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*
import kotlin.native.concurrent.*

private const val UNDECIDED = 0
private const val SUSPENDED = 1
private const val RESUMED = 2

@JvmField
@SharedImmutable
internal val RESUME_TOKEN = Symbol("RESUME_TOKEN")

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
     * CancellableContinuationImpl is a subset of Job with following limitations:
     * 1) It can have only cancellation listener (no "on cancelling")
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
        setupCancellation()
    }

    private fun isReusable(): Boolean = delegate is DispatchedContinuation<*> && delegate.isReusable(this)

    /**
     * Resets cancellability state in order to [suspendCancellableCoroutineReusable] to work.
     * Invariant: used only by [suspendCancellableCoroutineReusable] in [REUSABLE_CLAIMED] state.
     */
    @JvmName("resetState") // Prettier stack traces
    internal fun resetState(resumeMode: Int): Boolean {
        assert { parentHandle !== NonDisposableHandle }
        val state = _state.value
        assert { state !is NotCompleted }
        if (state is CompletedContinuation && state.idempotentResume != null) {
            // Cannot reuse continuation that was resumed with idempotent marker
            detachChild()
            return false
        }
        _decision.value = UNDECIDED
        _state.value = Active
        this.resumeMode = resumeMode
        return true
    }

    /**
     * Setups parent cancellation and checks for postponed cancellation in the case of reusable continuations.
     * It is only invoked from an internal [getResult] function for reusable continuations
     * and from [suspendCancellableCoroutine] to establish a cancellation before registering CC anywhere.
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
        if (!resumeMode.isReusableMode) return completed // Do not check postponed cancellation for non-reusable continuations
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

    override fun cancelCompletedResult(cause: Throwable): Unit = _state.loop { state ->
        when (state) {
            is NotCompleted -> error("Not completed")
            is CompletedExceptionally -> return // already completed exception or cancelled, nothing to do
            is CompletedContinuation -> {
                check(!state.cancelled) { "Must be called at most once" }
                val update = state.copy(cancelCause = cause)
                if (_state.compareAndSet(state, update)) {
                    state.invokeHandlers(this, cause)
                    return // done
                }
            }
            else -> {
                // completed normally without marker class, promote to CompletedContinuation to synchronize cancellation
                if (_state.compareAndSet(state, CompletedContinuation(state, cancelCause = cause))) return
            }
        }
    }

    /*
     * Attempt to postpone cancellation for reusable cancellable continuation
     */
    private fun cancelLater(cause: Throwable): Boolean {
        if (!resumeMode.isReusableMode) return false
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
            dispatchResume(mode = MODE_ATOMIC) // no need for additional cancellation checks
            return true
        }
    }

    internal fun parentCancelled(cause: Throwable) {
        if (cancelLater(cause)) return
        cancel(cause)
        // Even if cancellation has failed, we should detach child to avoid potential leak
        detachChildIfNonResuable()
    }

    internal inline fun invokeHandlerSafely(block: () -> Unit) {
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
        // otherwise, there is a race if suspendCancellableCoroutine { cont -> ... } does cont.resume(...)
        // before the block returns. This getResult would return a result as opposed to cancellation
        // exception that should have happened if the continuation is dispatched for execution later.
        if (resumeMode.isCancellableMode) {
            val job = context[Job]
            if (job != null && !job.isActive) {
                val cause = job.getCancellationException()
                cancelCompletedResult(cause)
                throw recoverStackTrace(cause, this)
            }
        }
        return getSuccessfulResult(state)
    }

    override fun resumeWith(result: Result<T>) =
        resumeImpl(result.toState(this), resumeMode)

    override fun resume(value: T, onCancellation: (cause: Throwable) -> Unit) =
        resumeImpl(value, resumeMode, onCancellation)

    public override fun invokeOnCancellation(handler: CompletionHandler) {
        val cancelHandler = makeCancelHandler(handler)
        _state.loop { state ->
            when (state) {
                is Active -> {
                    if (_state.compareAndSet(state, cancelHandler)) return // quit on cas success
                }
                is CancelHandler -> multipleHandlersError(handler, state)
                is CompletedExceptionally -> {
                    /*
                     * Continuation was already cancelled or completed exceptionally.
                     * NOTE: multiple invokeOnCancellation calls with different handlers are not allowed,
                     * so we check to make sure handler was installed just once.
                     */
                    if (!state.makeHandled()) multipleHandlersError(handler, state)
                    /*
                     * Call the handler only if it was cancelled (not called when completed exceptionally).
                     * :KLUDGE: We have to invoke a handler in platform-specific way via `invokeIt` extension,
                     * because we play type tricks on Kotlin/JS and handler is not necessarily a function there
                     */
                    if (state is CancelledContinuation) {
                        invokeHandlerSafely { handler.invokeIt((state as? CompletedExceptionally)?.cause) }
                    }
                    return
                }
                is CompletedContinuation -> {
                    /*
                     * Continuation was already completed, and might already have cancel handler.
                     */
                    if (state.cancelHandler != null) multipleHandlersError(handler, state)
                    if (state.cancelled) {
                        // todo: extra layer of protection against the second invokeOnCancellation
                        // if (!state.makeHandled()) multipleHandlersError(handler, state)
                        // Was already cancelled while being dispatched -- invoke the handler directly
                        invokeHandlerSafely { handler.invokeIt(state.cancelCause) }
                        return
                    }
                    val update = state.copy(cancelHandler = cancelHandler)
                    if (_state.compareAndSet(state, update)) return // quit on cas success
                }
                else -> {
                    /*
                     * Continuation was already completed normally, but might get cancelled while being dispatched.
                     * Change its state to CompletedContinuation.
                     */
                    val update = CompletedContinuation(state, cancelHandler = cancelHandler)
                    if (_state.compareAndSet(state, update)) return // quit on cas success
                }
            }
        }
    }

    private fun multipleHandlersError(handler: CompletionHandler, state: Any?) {
        error("It's prohibited to register multiple handlers, tried to register $handler, already has $state")
    }

    private fun makeCancelHandler(handler: CompletionHandler): CancelHandler =
        if (handler is CancelHandler) handler else InvokeOnCancel(handler)

    private fun dispatchResume(mode: Int) {
        if (tryResume()) return // completed before getResult invocation -- bail out
        // otherwise, getResult has already commenced, i.e. completed later or in other thread
        dispatch(mode)
    }

    private fun resumedState(
        state: NotCompleted,
        proposedUpdate: Any?,
        resumeMode: Int,
        onCancellation: ((cause: Throwable) -> Unit)?,
        idempotent: Any?
    ): Any? = when {
        proposedUpdate is CompletedExceptionally -> {
            assert { idempotent == null } // there are no idempotent exceptional resumes
            assert { onCancellation == null } // only successful results can be cancelled
            proposedUpdate
        }
        !resumeMode.isCancellableMode && idempotent == null -> proposedUpdate // cannot be cancelled in process, all is fine
        onCancellation != null || state is CancelHandler || idempotent != null ->
            // mark as CompletedContinuation if special cases are present (cancellation handlers or idempotent resume)
            CompletedContinuation(proposedUpdate, state as? CancelHandler, onCancellation, idempotent)
        else -> proposedUpdate // simple case -- use the value directly
    }

    private fun resumeImpl(
        proposedUpdate: Any?,
        resumeMode: Int,
        onCancellation: ((cause: Throwable) -> Unit)? = null
    ) {
        _state.loop { state ->
            when (state) {
                is NotCompleted -> {
                    val update = resumedState(state, proposedUpdate, resumeMode, onCancellation, idempotent = null)
                    if (!_state.compareAndSet(state, update)) return@loop // retry on cas failure
                    detachChildIfNonResuable()
                    dispatchResume(resumeMode) // dispatch resume, but it might get cancelled in process
                    return // done
                }
                is CancelledContinuation -> {
                    /*
                     * If continuation was cancelled, then resume attempt must be ignored,
                     * because cancellation is asynchronous and may race with resume.
                     * Racy exceptions will be lost, too.
                     */
                    if (state.makeResumed()) { // check if trying to resume one (otherwise error)
                        // call onCancellation
                        onCancellation?.let { invokeHandlerSafely { it(state.cause) } }
                        return // done
                    }
                }
            }
            alreadyResumedError(proposedUpdate) // otherwise, an error (second resume attempt)
        }
    }

    /**
     * Similar to [tryResume], but does not actually completes resume (needs [completeResume] call).
     * Returns [RESUME_TOKEN] when resumed, `null` when it was already resumed or cancelled.
     */
    private fun tryResumeImpl(
        proposedUpdate: Any?,
        idempotent: Any?,
        onCancellation: ((cause: Throwable) -> Unit)?
    ): Symbol? {
        _state.loop { state ->
            when (state) {
                is NotCompleted -> {
                    val update = resumedState(state, proposedUpdate, resumeMode, onCancellation, idempotent)
                    if (!_state.compareAndSet(state, update)) return@loop // retry on cas failure
                    detachChildIfNonResuable()
                    return RESUME_TOKEN
                }
                is CompletedContinuation -> {
                    return if (idempotent != null && state.idempotentResume === idempotent) {
                        assert { state.result === proposedUpdate } // "Non-idempotent resume"
                        RESUME_TOKEN // resumed with the same token -- ok
                    } else {
                        null // resumed with a different token or non-idempotent -- too late
                    }
                }
                else -> return null // cannot resume -- not active anymore
            }
        }
    }

    private fun alreadyResumedError(proposedUpdate: Any?): Nothing {
        error("Already resumed, but proposed with update $proposedUpdate")
    }

    // Unregister from parent job
    private fun detachChildIfNonResuable() {
        // If instance is reusable, do not detach on every reuse, #releaseInterceptedContinuation will do it for us in the end
        if (!isReusable()) detachChild()
    }

    /**
     * Detaches from the parent.
     * Invariant: used from [CoroutineDispatcher.releaseInterceptedContinuation] iff [isReusable] is `true`
     */
    internal fun detachChild() {
        val handle = parentHandle
        handle?.dispose()
        parentHandle = NonDisposableHandle
    }

    // Note: Always returns RESUME_TOKEN | null
    override fun tryResume(value: T, idempotent: Any?): Any? =
        tryResumeImpl(value, idempotent = idempotent, onCancellation = null)

    override fun tryResumeAtomic(value: T, idempotent: Any?, onCancellation: (cause: Throwable) -> Unit): Any? =
        tryResumeImpl(value, idempotent, onCancellation)

    override fun tryResumeWithException(exception: Throwable): Any? =
        tryResumeImpl(CompletedExceptionally(exception), idempotent = null, onCancellation = null)

    // note: token is always RESUME_TOKEN
    override fun completeResume(token: Any) {
        assert { token === RESUME_TOKEN }
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
            is CompletedContinuation -> state.result as T
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

// Completed with additional metadata
private data class CompletedContinuation(
    @JvmField val result: Any?,
    @JvmField val cancelHandler: CancelHandler? = null, // installed via invokeOnCancellation
    @JvmField val onCancellation: ((cause: Throwable) -> Unit)? = null, // installed via resume block
    @JvmField val idempotentResume: Any? = null,
    @JvmField val cancelCause: Throwable? = null
) {
    val cancelled: Boolean get() = cancelCause != null

    fun invokeHandlers(cont: CancellableContinuationImpl<*>, cause: Throwable) {
        cancelHandler?.let { cont.invokeHandlerSafely { it.invoke(cause) } }
        onCancellation?.let { cont.invokeHandlerSafely { it.invoke(cause) } }
    }
}
