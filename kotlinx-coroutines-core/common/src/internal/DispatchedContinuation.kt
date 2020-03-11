/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlin.native.concurrent.*

@SharedImmutable
private val UNDEFINED = Symbol("UNDEFINED")
@SharedImmutable
@JvmField
internal val REUSABLE_CLAIMED = Symbol("REUSABLE_CLAIMED")

internal class DispatchedContinuation<in T>(
    @JvmField val dispatcher: CoroutineDispatcher,
    @JvmField val continuation: Continuation<T>
) : DispatchedTask<T>(MODE_ATOMIC_DEFAULT), CoroutineStackFrame, Continuation<T> by continuation {
    @JvmField
    @Suppress("PropertyName")
    internal var _state: Any? = UNDEFINED
    override val callerFrame: CoroutineStackFrame? = continuation as? CoroutineStackFrame
    override fun getStackTraceElement(): StackTraceElement? = null
    @JvmField // pre-cached value to avoid ctx.fold on every resumption
    internal val countOrElement = threadContextElements(context)

    /**
     * Possible states of reusability:
     *
     * 1) `null`. Cancellable continuation wasn't yet attempted to be reused or
     *     was used and then invalidated (e.g. because of the cancellation).
     * 2) [CancellableContinuation]. Continuation to be/that is being reused.
     * 3) [REUSABLE_CLAIMED]. CC is currently being reused and its owner executes `suspend` block:
     *    ```
     *    // state == null | CC
     *    suspendAtomicCancellableCoroutineReusable { cont ->
     *        // state == REUSABLE_CLAIMED
     *        block(cont)
     *    }
     *    // state == CC
     *    ```
     * 4) [Throwable] continuation was cancelled with this cause while being in [suspendAtomicCancellableCoroutineReusable],
     *    [CancellableContinuationImpl.getResult] will check for cancellation later.
     *
     * [REUSABLE_CLAIMED] state is required to prevent the lost resume in the channel.
     * AbstractChannel.receive method relies on the fact that the following pattern
     * ```
     * suspendAtomicCancellableCoroutineReusable { cont ->
     *     val result = pollFastPath()
     *     if (result != null) cont.resume(result)
     * }
     * ```
     * always succeeds.
     * To make it always successful, we actually postpone "reusable" cancellation
     * to this phase and set cancellation only at the moment of instantiation.
     */
    private val _reusableCancellableContinuation = atomic<Any?>(null)

    public val reusableCancellableContinuation: CancellableContinuationImpl<*>?
        get() = _reusableCancellableContinuation.value as? CancellableContinuationImpl<*>

    public fun isReusable(requester: CancellableContinuationImpl<*>): Boolean {
        /*
         * Reusability control:
         * `null` -> no reusability at all, false
         * If current state is not CCI, then we are within `suspendAtomicCancellableCoroutineReusable`, true
         * Else, if result is CCI === requester.
         * Identity check my fail for the following pattern:
         * ```
         * loop:
         * suspendAtomicCancellableCoroutineReusable { } // Reusable, outer coroutine stores the child handle
         * suspendCancellableCoroutine { } // **Not reusable**, handle should be disposed after {}, otherwise
         * it will leak because it won't be freed by `releaseInterceptedContinuation`
         * ```
         */
        val value = _reusableCancellableContinuation.value ?: return false
        if (value is CancellableContinuationImpl<*>) return value === requester
        return true
    }

    /**
     * Claims the continuation for [suspendAtomicCancellableCoroutineReusable] block,
     * so all cancellations will be postponed.
     */
    @Suppress("UNCHECKED_CAST")
    fun claimReusableCancellableContinuation(): CancellableContinuationImpl<T>? {
        /*
         * Transitions:
         * 1) `null` -> claimed, caller will instantiate CC instance
         * 2) `CC` -> claimed, caller will reuse CC instance
         */
        _reusableCancellableContinuation.loop { state ->
            when {
                state === null -> {
                    /*
                     * null -> CC was not yet published -> we do not compete with cancel
                     * -> can use plain store instead of CAS
                     */
                    _reusableCancellableContinuation.value = REUSABLE_CLAIMED
                    return null
                }
                state is CancellableContinuationImpl<*> -> {
                    if (_reusableCancellableContinuation.compareAndSet(state, REUSABLE_CLAIMED)) {
                        return state as CancellableContinuationImpl<T>
                    }
                }
                else -> error("Inconsistent state $state")
            }
        }
    }

    /**
     * Checks whether there were any attempts to cancel reusable CC while it was in [REUSABLE_CLAIMED] state
     * and returns cancellation cause if so, `null` otherwise.
     * If continuation was cancelled, it becomes non-reusable.
     *
     * ```
     * suspendAtomicCancellableCoroutineReusable { // <- claimed
     * // Any asynchronous cancellation is "postponed" while this block
     * // is being executed
     * } // postponed cancellation is checked here in `getResult`
     * ```
     *
     * See [CancellableContinuationImpl.getResult].
     */
    fun checkPostponedCancellation(continuation: CancellableContinuation<*>): Throwable? {
        _reusableCancellableContinuation.loop { state ->
            // not when(state) to avoid Intrinsics.equals call
            when {
                state === REUSABLE_CLAIMED -> {
                    if (_reusableCancellableContinuation.compareAndSet(REUSABLE_CLAIMED, continuation)) return null
                }
                state === null -> return null
                state is Throwable -> {
                    require(_reusableCancellableContinuation.compareAndSet(state, null))
                    return state
                }
                else -> error("Inconsistent state $state")
            }
        }
    }

    /**
     * Tries to postpone cancellation if reusable CC is currently in [REUSABLE_CLAIMED] state.
     * Returns `true` if cancellation is (or previously was) postponed, `false` otherwise.
     */
    fun postponeCancellation(cause: Throwable): Boolean {
        _reusableCancellableContinuation.loop { state ->
            when (state) {
                REUSABLE_CLAIMED -> {
                    if (_reusableCancellableContinuation.compareAndSet(REUSABLE_CLAIMED, cause))
                        return true
                }
                is Throwable -> return true
                else -> {
                    // Invalidate
                    if (_reusableCancellableContinuation.compareAndSet(state, null))
                        return false
                }
            }
        }
    }

    override fun takeState(): Any? {
        val state = _state
        assert { state !== UNDEFINED } // fail-fast if repeatedly invoked
        _state = UNDEFINED
        return state
    }

    override val delegate: Continuation<T>
        get() = this

    override fun resumeWith(result: Result<T>) {
        val context = continuation.context
        val state = result.toState()
        if (dispatcher.isDispatchNeeded(context)) {
            _state = state
            resumeMode = MODE_ATOMIC_DEFAULT
            dispatcher.dispatch(context, this)
        } else {
            executeUnconfined(state, MODE_ATOMIC_DEFAULT) {
                withCoroutineContext(this.context, countOrElement) {
                    continuation.resumeWith(result)
                }
            }
        }
    }

    // We inline it to save an entry on the stack in cases where it shows (unconfined dispatcher)
    // It is used only in Continuation<T>.resumeCancellableWith
    @Suppress("NOTHING_TO_INLINE")
    inline fun resumeCancellableWith(result: Result<T>) {
        val state = result.toState()
        if (dispatcher.isDispatchNeeded(context)) {
            _state = state
            resumeMode = MODE_CANCELLABLE
            dispatcher.dispatch(context, this)
        } else {
            executeUnconfined(state, MODE_CANCELLABLE) {
                if (!resumeCancelled()) {
                    resumeUndispatchedWith(result)
                }
            }
        }
    }

    @Suppress("NOTHING_TO_INLINE")
    inline fun resumeCancelled(): Boolean {
        val job = context[Job]
        if (job != null && !job.isActive) {
            resumeWithException(job.getCancellationException())
            return true
        }

        return false
    }

    @Suppress("NOTHING_TO_INLINE") // we need it inline to save us an entry on the stack
    inline fun resumeUndispatchedWith(result: Result<T>) {
        withCoroutineContext(context, countOrElement) {
            continuation.resumeWith(result)
        }
    }

    // used by "yield" implementation
    internal fun dispatchYield(context: CoroutineContext, value: T) {
        _state = value
        resumeMode = MODE_CANCELLABLE
        dispatcher.dispatchYield(context, this)
    }

    override fun toString(): String =
        "DispatchedContinuation[$dispatcher, ${continuation.toDebugString()}]"
}

/**
 * It is not inline to save bytecode (it is pretty big and used in many places)
 * and we leave it public so that its name is not mangled in use stack traces if it shows there.
 * It may appear in stack traces when coroutines are started/resumed with unconfined dispatcher.
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun <T> Continuation<T>.resumeCancellableWith(result: Result<T>) = when (this) {
    is DispatchedContinuation -> resumeCancellableWith(result)
    else -> resumeWith(result)
}

internal fun DispatchedContinuation<Unit>.yieldUndispatched(): Boolean =
    executeUnconfined(Unit, MODE_CANCELLABLE, doYield = true) {
        run()
    }

/**
 * Executes given [block] as part of current event loop, updating current continuation
 * mode and state if continuation is not resumed immediately.
 * [doYield] indicates whether current continuation is yielding (to provide fast-path if event-loop is empty).
 * Returns `true` if execution of continuation was queued (trampolined) or `false` otherwise.
 */
private inline fun DispatchedContinuation<*>.executeUnconfined(
    contState: Any?, mode: Int, doYield: Boolean = false,
    block: () -> Unit
): Boolean {
    val eventLoop = ThreadLocalEventLoop.eventLoop
    // If we are yielding and unconfined queue is empty, we can bail out as part of fast path
    if (doYield && eventLoop.isUnconfinedQueueEmpty) return false
    return if (eventLoop.isUnconfinedLoopActive) {
        // When unconfined loop is active -- dispatch continuation for execution to avoid stack overflow
        _state = contState
        resumeMode = mode
        eventLoop.dispatchUnconfined(this)
        true // queued into the active loop
    } else {
        // Was not active -- run event loop until all unconfined tasks are executed
        runUnconfinedEventLoop(eventLoop, block = block)
        false
    }
}
