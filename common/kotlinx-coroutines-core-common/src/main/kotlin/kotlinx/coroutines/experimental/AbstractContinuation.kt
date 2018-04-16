/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.internalAnnotations.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

private const val UNDECIDED = 0
private const val SUSPENDED = 1
private const val RESUMED = 2

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
internal abstract class AbstractContinuation<in T>(
    public final override val delegate: Continuation<T>,
    public final override val resumeMode: Int
) : Continuation<T>, DispatchedTask<T> {

    /*
     * AbstractContinuation is a subset of Job with following limitations:
     * 1) It can have only cancellation listeners
     * 2) It always invokes cancellation listener if it's cancelled (no 'invokeImmediately')
     * 3) It can have at most one cancellation listener
     * 4) It cannot be in cancelling state, only active/finished/cancelled
     * 5) Its cancellation listeners cannot be deregistered
     *
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
       SINGLE_A    CancellationHandler  : Active        active, one cancellation listener
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
        val handle = parent.invokeOnCompletion(onCancelling = true, handler = ChildContinuation(parent, this).asHandler)

        parentHandle = handle
        // now check our state _after_ registering (see updateState order of actions)
        if (isCompleted) {
            handle.dispose()
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
    }

    override fun takeState(): Any? = state

    public fun cancel(cause: Throwable?): Boolean {
        loopOnState { state ->
            if (state !is NotCompleted) return false // quit if already complete
            if (updateStateCancelled(state, cause)) return true
        }
    }

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
        if (state is CompletedExceptionally) throw state.exception
        return getSuccessfulResult(state)
    }

    override fun resume(value: T) =
        resumeImpl(value, resumeMode)

    override fun resumeWithException(exception: Throwable) =
        resumeImpl(CompletedExceptionally(exception), resumeMode)

    public fun invokeOnCancellation(handler: CompletionHandler) {
        var handleCache: CancellationHandler? = null
        loopOnState { state ->
            when (state) {
                is Active -> {
                    val node = handleCache ?: makeHandler(handler).also { handleCache = it }
                    if (_state.compareAndSet(state, node)) {
                        return
                    }
                }
                is CancellationHandler -> error("It's prohibited to register multiple handlers, tried to register $handler, already has $state")
                is CancelledContinuation -> {
                    /*
                     * Continuation is complete, invoke directly.
                     * NOTE: multiple invokeOnCancellation calls with different handlers are allowed on completed coroutine.
                     * It's slightly inconsistent with running coroutine, but currently, we have no mechanism to check
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

    private fun updateStateCancelled(state: NotCompleted, cause: Throwable?): Boolean =
        updateState(state, CancelledContinuation(this, cause), mode = MODE_ATOMIC_DEFAULT)

    private fun onCompletionInternal(mode: Int) {
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
                    if (updateState(state, proposedUpdate, resumeMode)) return
                }

                is CancelledContinuation -> {
                    if (proposedUpdate !is CompletedExceptionally) {
                        return // Cancelled continuation completed, do nothing
                    }

                    /*
                     * Coerce concurrent cancellation and pending thrown exception.
                     * E.g. for linear history `T1: cancel() T2 (job): throw e T3: job.await()`
                     * we'd like to see actual exception in T3, not JobCancellationException.
                     * So thrown exception overwrites cancellation exception, but
                     * suppresses its non-null cause.
                     */
                    if (state.exception is CancellationException && state.exception.cause == null) {
                        return // Do not add to suppressed regular cancellation
                    }

                    if (state.exception is CancellationException && state.exception.cause === proposedUpdate.exception) {
                        return // Do not add to suppressed cancellation with the same cause
                    }

                    if (state.exception === proposedUpdate.exception) {
                        return // Do no add to suppressed the same exception
                    }

                    val exception = proposedUpdate.exception
                    val update = CompletedExceptionally(exception)
                    if (state.cause != null) {
                        exception.addSuppressedThrowable(state.cause)
                    }

                    if (_state.compareAndSet(state, update)) {
                        return
                    }
                }

                else -> error("Already resumed, but proposed with update $proposedUpdate")
            }
        }
    }

    private fun makeHandler(handler: CompletionHandler): CancellationHandlerImpl<*> {
        if (handler is CancellationHandlerImpl<*>) {
            require(handler.continuation === this) { "Handler has non-matching continuation ${handler.continuation}, current: $this" }
            return handler
        }

        return InvokeOnCancel(this, handler)
    }

    private fun handleException(exception: Throwable) {
        handleCoroutineException(context, exception)
    }

    private fun updateState(expect: NotCompleted, proposedUpdate: Any?, mode: Int): Boolean {
        if (!tryUpdateState(expect, proposedUpdate)) {
            return false
        }

        completeUpdateState(expect, proposedUpdate, mode)
        return true
    }

    /**
     * Completes update of the current [state] of this job.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun completeUpdateState(expect: NotCompleted, update: Any?, mode: Int) {
        val exceptionally = update as? CompletedExceptionally
        onCompletionInternal(mode)

        // Invoke cancellation handlers only if necessary
        if (update is CancelledContinuation && expect is CancellationHandler) {
            try {
                expect.invoke(exceptionally?.cause)
            } catch (ex: Throwable) {
                handleException(CompletionHandlerException("Exception in completion handler $expect for $this", ex))
            }
        }
    }

    /**
     * Tries to initiate update of the current [state] of this job.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun tryUpdateState(expect: NotCompleted, update: Any?): Boolean {
        require(update !is NotCompleted) // only NotCompleted -> completed transition is allowed
        if (!_state.compareAndSet(expect, update)) return false
        // Unregister from parent job
        parentHandle?.let {
            it.dispose() // volatile read parentHandle _after_ state was updated
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
        return true // continues in completeUpdateState
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

internal abstract class CancellationHandlerImpl<out C : AbstractContinuation<*>>(@JvmField val continuation: C) :
    CancellationHandler(), NotCompleted

// Wrapper for lambdas, for the performance sake CancellationHandler can be subclassed directly
private class InvokeOnCancel( // Clashes with InvokeOnCancellation
    continuation: AbstractContinuation<*>,
    private val handler: CompletionHandler
) : CancellationHandlerImpl<AbstractContinuation<*>>(continuation) {

    override fun invoke(cause: Throwable?) {
        handler.invoke(cause)
    }

    override fun toString() = "InvokeOnCancel[${handler.classSimpleName}@$hexAddress]"
}
