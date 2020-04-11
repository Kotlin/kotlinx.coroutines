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
        if (state is CompletedIdempotentResult) {
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
            is CancelledContinuation -> return // already cancelled, nothing to do
            is CompletedWithCancelHandler -> {
                check(!state.cancelled) { "Must be called at most once" }
                val update = state.withCancelCause(cause)
                if (_state.compareAndSet(state, update)) {
                    state.invokeHandler(this, cause)
                    return // done
                }
            }
            else -> {
                // completed normally without marker class, set CompletedWithCancelHandler to synchronize cancellation
                if (_state.compareAndSet(state, CompletedWithCancelHandler(state, null, cause))) return
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
                     * Call handler only if it was cancelled.
                     * :KLUDGE: We have to invoke a handler in platform-specific way via `invokeIt` extension,
                     * because we play type tricks on Kotlin/JS and handler is not necessarily a function there
                     */
                    if (state is CancelledContinuation) {
                        invokeHandlerSafely { handler.invokeIt((state as? CompletedExceptionally)?.cause) }
                    }
                    return
                }
                is CompletedWithCancelHandler -> {
                    /*
                     * Continuation was already completed, and might already have cancel handler.
                     */
                    if (state.cancelHandler != null) multipleHandlersError(handler, state)
                    if (state.cancelled) {
                        // Was already cancelled while being dispatched -- invoke the handler directly
                        invokeHandlerSafely { handler.invokeIt(state.cancelCause) }
                        return
                    }
                    val update = state.withCancelHandler(cancelHandler)
                    if (_state.compareAndSet(state, update)) return // quit on cas success
                }
                else -> {
                    /*
                     * Continuation was already completed, but might get cancelled while being dispatched.
                     * Change its state to CompletedWithCancelHandler.
                     */
                    val update = CompletedWithCancelHandler(state, cancelHandler, null)
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

    // returns null when successfully dispatched resumed, CancelledContinuation if too late (was already cancelled)
    private fun resumeImpl(
        proposedUpdate: Any?,
        resumeMode: Int,
        onCancellation: ((cause: Throwable) -> Unit)? = null
    ) {
        _state.loop { state ->
            when (state) {
                is NotCompleted -> {
                    val update = when {
                        proposedUpdate is CompletedExceptionally -> proposedUpdate // only successful results can be cancelled
                        !resumeMode.isCancellableMode -> proposedUpdate // cannot be cancelled in process, all is fine
                        onCancellation != null -> CompletedWithOnCancellation(proposedUpdate, state as? CancelHandler, onCancellation)
                        state is CancelHandler -> CompletedWithCancelHandler(proposedUpdate, state)
                        else -> proposedUpdate
                    }
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
     * Invariant: used from [CoroutineDispatcher.releaseInterceptedContinuation] iff [isReusable] is `true`
     */
    internal fun detachChild() {
        val handle = parentHandle
        handle?.dispose()
        parentHandle = NonDisposableHandle
    }

    // Note: Always returns RESUME_TOKEN | null
    override fun tryResume(value: T, idempotent: Any?): Any? {
        _state.loop { state ->
            when (state) {
                is NotCompleted -> {
                    val update: Any? = when {
                        idempotent != null -> CompletedIdempotentResult(idempotent, value, state as? CancelHandler)
                        state is CancelHandler -> CompletedWithCancelHandler(value, state)
                        else -> value
                    }
                    if (!_state.compareAndSet(state, update)) return@loop // retry on cas failure
                    detachChildIfNonResuable()
                    return RESUME_TOKEN
                }
                is CompletedIdempotentResult -> {
                    return if (state.idempotentResume === idempotent) {
                        assert { state.result === value } // "Non-idempotent resume"
                        RESUME_TOKEN
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
                    return RESUME_TOKEN
                }
                else -> return null // cannot resume -- not active anymore
            }
        }
    }

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
            is CompletedWithCancelHandler -> state.result as T
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

private open class CompletedWithCancelHandler(
    @JvmField val result: Any?,
    @JvmField val cancelHandler: CancelHandler?, // installed via invokeOnCancellation
    @JvmField val cancelCause: Throwable? = null
) {
    val cancelled: Boolean get() = cancelCause != null

    open fun invokeHandler(cont: CancellableContinuationImpl<*>, cause: Throwable) {
        cancelHandler?.let { cont.invokeHandlerSafely { it.invoke(cause) } }
    }

    open fun withCancelCause(cancelCause: Throwable): CompletedWithCancelHandler =
        CompletedWithCancelHandler(result, cancelHandler, cancelCause)

    open fun withCancelHandler(cancelHandler: CancelHandler): CompletedWithCancelHandler =
        CompletedWithCancelHandler(result, cancelHandler, cancelCause)

    override fun toString(): String = "$classSimpleName[$result]"
}

private class CompletedIdempotentResult(
    @JvmField val idempotentResume: Any?,
    result: Any?,
    cancelHandler: CancelHandler?,
    cancelCause: Throwable? = null
) : CompletedWithCancelHandler(result, cancelHandler, cancelCause) {
    override fun withCancelCause(cancelCause: Throwable): CompletedWithCancelHandler =
        CompletedIdempotentResult(idempotentResume, result, cancelHandler, cancelCause)

    override fun withCancelHandler(cancelHandler: CancelHandler): CompletedWithCancelHandler =
        CompletedIdempotentResult(idempotentResume, result, cancelHandler, cancelCause)
}

private class CompletedWithOnCancellation(
    result: Any?,
    cancelHandler: CancelHandler?, // installed via invokeOnCancellation
    @JvmField val onCancellation: (cause: Throwable) -> Unit, // installed via resume block
    cancelCause: Throwable? = null
) : CompletedWithCancelHandler(result, cancelHandler, cancelCause) {
    override fun invokeHandler(cont: CancellableContinuationImpl<*>, cause: Throwable) {
        super.invokeHandler(cont, cause)
        cont.invokeHandlerSafely { onCancellation.invoke(cause) }
    }

    override fun withCancelCause(cancelCause: Throwable): CompletedWithCancelHandler =
        CompletedWithOnCancellation(result, cancelHandler, onCancellation, cancelCause)

    override fun withCancelHandler(cancelHandler: CancelHandler): CompletedWithCancelHandler =
        CompletedWithOnCancellation(result, cancelHandler, onCancellation, cancelCause)
}
