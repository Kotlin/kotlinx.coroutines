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
     * Implementation notes
     *
     * AbstractContinuation is a subset of Job with following limitations:
     * 1) It can have only cancellation listeners
     * 2) It always invokes cancellation listener if it's cancelled (no 'invokeImmediately')
     * 3) It can have at most one cancellation listener
     * 4) Its cancellation listeners cannot be deregistered
     * As a consequence it has much simpler state machine, more lightweight machinery and
     * less dependencies.
     *
     * Cancelling state
     * If useCancellingState is true, then this continuation can have additional cancelling state,
     * which is transition from Active to Cancelled. This is specific state to support withContext(ctx)
     * construction: block in withContext can be cancelled from withing or even before stepping into withContext,
     * but we still want to properly run it (e.g. when it has atomic cancellation mode) and run its completion listener
     * after.
     * During cancellation all pending exceptions are aggregated and thrown during transition to final state
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
       CANCELLING  Cancelling           : Active        in the process of cancellation due to cancellation of parent job
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

    protected open val useCancellingState: Boolean get() = false

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

    public fun cancel(cause: Throwable?): Boolean {
        loopOnState { state ->
            if (state !is NotCompleted) return false // quit if already complete
            if (state is Cancelling) return false // someone else succeeded
            if (tryCancel(state, cause)) return true
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
        if (state is CompletedExceptionally) throw state.cause
        return getSuccessfulResult(state)
    }

    override fun resume(value: T) =
        resumeImpl(value, resumeMode)

    override fun resumeWithException(exception: Throwable) =
        resumeImpl(CompletedExceptionally(exception), resumeMode)

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
                is Cancelling -> error("Cancellation handlers for continuations with 'Cancelling' state are not supported")
                else -> return
            }
        }
    }

    private fun makeHandler(handler: CompletionHandler): CancelHandler =
        if (handler is CancelHandler) handler else InvokeOnCancel(handler)

    private fun tryCancel(state: NotCompleted, cause: Throwable?): Boolean {
        if (useCancellingState) {
            require(state !is CancelHandler) { "Invariant: 'Cancelling' state and cancellation handlers cannot be used together" }
            return _state.compareAndSet(state, Cancelling(CancelledContinuation(this, cause)))
        }

        return updateStateToFinal(state, CancelledContinuation(this, cause), mode = MODE_ATOMIC_DEFAULT)
    }

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
                is Cancelling -> { // withContext() support
                    /*
                     * If already cancelled block is resumed with non-exception,
                     * resume it with cancellation exception.
                     * E.g.
                     * ```
                     * val value = withContext(ctx) {
                     *   outerJob.cancel() // -> cancelling
                     *   42 // -> cancelled
                     * }
                     * ```
                     * should throw cancellation exception instead of returning 42
                     */
                    if (proposedUpdate !is CompletedExceptionally) {
                        val update = state.cancel
                        if (updateStateToFinal(state, update, resumeMode)) return
                    } else {
                        /*
                         * If already cancelled block is resumed with an exception,
                         * then we should properly merge them to avoid information loss.
                         *
                         * General rule:
                         * Thrown exception always becomes a result and cancellation reason
                         * is added to suppressed exceptions if necessary.
                         * Basic duplicate/cycles check is performed
                         */
                        val update: CompletedExceptionally

                        /*
                         * Proposed update is another CancellationException.
                         * e.g.
                         * ```
                         * T1: ctxJob.cancel(e1) // -> cancelling
                         * T2:
                         * withContext(ctx, Mode.ATOMIC) {
                         *   // -> resumed with cancellation exception
                         * }
                         * ```
                         */
                        if (proposedUpdate.cause is CancellationException) {
                            // Keep original cancellation cause and try add to suppressed exception from proposed cancel
                            update = proposedUpdate
                            coerceWithException(state, update)
                        } else {
                            /*
                             * Proposed update is exception => transition to terminal state
                             * E.g.
                             * ```
                             * withContext(ctx) {
                             *   outerJob.cancel() // -> cancelling
                             *   throw Exception() // -> completed exceptionally
                             * }
                             * ```
                             */
                            val exception = proposedUpdate.cause
                            val currentException = state.cancel.cause
                            // Add to suppressed if original cancellation differs from proposed exception
                            if (currentException !is CancellationException || currentException.cause !== exception) {
                                exception.addSuppressedThrowable(currentException)
                            }

                            update = CompletedExceptionally(exception)
                        }

                        if (updateStateToFinal(state, update, resumeMode)) {
                            return
                        }
                    }
                }

                is NotCompleted -> {
                    if (updateStateToFinal(state, proposedUpdate, resumeMode)) return
                }
                is CancelledContinuation -> {
                    if (proposedUpdate is NotCompleted || proposedUpdate is CompletedExceptionally) {
                        error("Unexpected update, state: $state, update: $proposedUpdate")
                    }
                    // Coroutine is dispatched normally (e.g.via `delay()`) after cancellation
                    return
                }
                else -> error("Already resumed, but proposed with update $proposedUpdate")
            }
        }
    }

    // Coerce current cancelling state with proposed exception
    private fun coerceWithException(state: Cancelling, proposedUpdate: CompletedExceptionally) {
        val originalCancellation = state.cancel
        val originalException = originalCancellation.cause
        val updateCause = proposedUpdate.cause
        // Cause of proposed update is present and differs from one in current state
        val isSameCancellation = originalCancellation.cause is CancellationException
                && originalException.cause === updateCause.cause
        if (!isSameCancellation && (originalException.cause !== updateCause)) {
            proposedUpdate.cause.addSuppressedThrowable(originalException)
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
        onCompletionInternal(mode)

        // Invoke cancellation handlers only if necessary
        if (update is CancelledContinuation && expect is CancelHandler) {
            try {
                expect.invoke(exceptionally?.cause)
            } catch (ex: Throwable) {
                handleException(CompletionHandlerException("Exception in completion handler $expect for $this", ex))
            }
        }
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

// In progress of cancellation
internal class Cancelling(@JvmField val cancel: CancelledContinuation) : NotCompleted

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
