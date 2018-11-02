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
internal abstract class AbstractContinuation<in T>(
    public final override val delegate: Continuation<T>,
    resumeMode: Int
) : DispatchedTask<T>(resumeMode), Continuation<T> {

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
       CANCELLED   Cancelled            : Cancelled     cancelled (final state)
       COMPLETED   any                  : Completed     produced some result or threw an exception (final state)
     */
    private val _state = atomic<Any?>(ACTIVE)

    @Volatile
    private var parentHandle: DisposableHandle? = null

    internal val state: Any? get() = _state.value

    public val isActive: Boolean get() = state is NotCompleted

    public val isCompleted: Boolean get() = state !is NotCompleted

    public val isCancelled: Boolean get() = state is CancelledContinuation

    internal fun initParentJobInternal(parent: Job?) {
        check(parentHandle == null)
        if (parent == null) {
            parentHandle = NonDisposableHandle
            return
        }
        parent.start() // make sure the parent is started
        val handle = parent.invokeOnCompletion(onCancelling = true,
            handler = ChildContinuation(parent, this).asHandler)

        parentHandle = handle
        // now check our state _after_ registering (see updateStateToFinal order of actions)
        if (isCompleted) {
            handle.dispose()
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
    }

    override fun takeState(): Any? = state

    public fun cancel(cause: Throwable?): Boolean =
        cancelImpl(cause)

    fun cancelImpl(cause: Throwable?): Boolean {
        loopOnState { state ->
            if (state !is NotCompleted) return false // quit if already complete
            val update = CancelledContinuation(this, cause)
            if (updateStateToFinal(state, update, mode = MODE_ATOMIC_DEFAULT)) return true
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

    public fun invokeOnCancellation(handler: CompletionHandler) {
        var handleCache: CancelHandler? = null
        loopOnState { state ->
            when (state) {
                is Active -> {
                    val node = handleCache ?: makeHandler(handler).also { handleCache = it }
                    if (_state.compareAndSet(state, node)) {
                        return
                    }
                }
                is CancelHandler -> error("It's prohibited to register multiple handlers, tried to register $handler, already has $state")
                is CancelledContinuation -> {
                    /*
                     * Continuation is complete, invoke directly.
                     * NOTE: multiple invokeOnCancellation calls with different handlers are allowed on cancelled continuation.
                     * It's inconsistent with running continuation, but currently, we have no mechanism to check
                     * whether any handler was registered during continuation lifecycle without additional overhead.
                     * This may be changed in the future.
                     *
                     * :KLUDGE: We have to invoke a handler in platform-specific way via `invokeIt` extension,
                     * because we play type tricks on Kotlin/JS and handler is not necessarily a function there
                     */
                    handler.invokeIt((state as? CompletedExceptionally)?.cause)
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

    protected inline fun loopOnState(block: (Any?) -> Unit): Nothing {
        while (true) {
            block(state)
        }
    }

    protected fun resumeImpl(proposedUpdate: Any?, resumeMode: Int) {
        loopOnState { state ->
            when (state) {
                is NotCompleted -> {
                    if (updateStateToFinal(state, proposedUpdate, resumeMode)) return
                }
                is CancelledContinuation -> {
                    /*
                     * If continuation was cancelled, then all further resumes must be
                     * ignored, because cancellation is asynchronous and may race with resume.
                     * Racy exception are reported so no exceptions are lost
                     *
                     * :todo: we should somehow remember the attempt to invoke resume and fail on the second attempt.
                     */
                    if (proposedUpdate is CompletedExceptionally) {
                        handleException(proposedUpdate.cause)
                    }
                    return
                }
                else -> error("Already resumed, but proposed with update $proposedUpdate")
            }
        }
    }

    /**
     * Tries to make transition from active to cancelled or completed state and invokes cancellation handler if necessary
     */
    private fun updateStateToFinal(expect: NotCompleted, proposedUpdate: Any?, mode: Int): Boolean {
        if (!tryUpdateStateToFinal(expect, proposedUpdate)) {
            return false
        }
        completeStateUpdate(expect, proposedUpdate, mode)
        return true
    }

    protected fun tryUpdateStateToFinal(expect: NotCompleted, update: Any?): Boolean {
        require(update !is NotCompleted) // only NotCompleted -> completed transition is allowed
        if (!_state.compareAndSet(expect, update)) return false
        // Unregister from parent job
        parentHandle?.let {
            it.dispose() // volatile read parentHandle _after_ state was updated
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
        return true // continues in completeStateUpdate
    }

    protected fun completeStateUpdate(expect: NotCompleted, update: Any?, mode: Int) {
        val exceptionally = update as? CompletedExceptionally

        if (update is CancelledContinuation && expect is CancelHandler) {
            try {
                expect.invoke(exceptionally?.cause)
            } catch (ex: Throwable) {
                handleException(CompletionHandlerException("Exception in completion handler $expect for $this", ex))
            }
        }

        // Notify all handlers before dispatching, otherwise behaviour will be timing-dependent
        // and confusing with Unconfined
        dispatchResume(mode)
    }

    private fun handleException(exception: Throwable) {
        handleCoroutineException(context, exception)
    }

    // For nicer debugging
    public override fun toString(): String =
        "${nameString()}{${stateString()}}@$hexAddress"

    protected open fun nameString(): String = classSimpleName

    private fun stateString(): String {
        val state = this.state
        return when (state) {
            is NotCompleted ->"Active"
            is CancelledContinuation -> "Cancelled"
            is CompletedExceptionally -> "CompletedExceptionally"
            else -> "Completed"
        }
    }

}

// Marker for active continuation
internal interface NotCompleted

private class Active : NotCompleted
private val ACTIVE: Active = Active()

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
