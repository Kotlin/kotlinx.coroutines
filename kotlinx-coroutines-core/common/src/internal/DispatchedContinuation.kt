/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.jvm.*

private val UNDEFINED = Symbol("UNDEFINED")
@JvmField
internal val REUSABLE_CLAIMED = Symbol("REUSABLE_CLAIMED")

internal class DispatchedContinuation<in T>(
    @JvmField val dispatcher: CoroutineDispatcher,
    @JvmField val continuation: Continuation<T>
) : DispatchedTask<T>(MODE_UNINITIALIZED), CoroutineStackFrame, Continuation<T> by continuation {
    @JvmField
    @Suppress("PropertyName")
    internal var _state: Any? = UNDEFINED
    override val callerFrame: CoroutineStackFrame? get() = continuation as? CoroutineStackFrame
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
     *    suspendCancellableCoroutineReusable { cont ->
     *        // state == REUSABLE_CLAIMED
     *        block(cont)
     *    }
     *    // state == CC
     *    ```
     * 4) [Throwable] continuation was cancelled with this cause while being in [suspendCancellableCoroutineReusable],
     *    [CancellableContinuationImpl.getResult] will check for cancellation later.
     *
     * [REUSABLE_CLAIMED] state is required to prevent double-use of the reused continuation.
     * In the `getResult`, we have the following code:
     * ```
     * if (trySuspend()) {
     *     // <- at this moment current continuation can be redispatched and claimed again.
     *     attachChildToParent()
     *     releaseClaimedContinuation()
     * }
     * ```
     */
    private val _reusableCancellableContinuation = atomic<Any?>(null)

    private val reusableCancellableContinuation: CancellableContinuationImpl<*>?
        get() = _reusableCancellableContinuation.value as? CancellableContinuationImpl<*>

    fun isReusable(): Boolean {
        /*
        Invariant: caller.resumeMode.isReusableMode
         * Reusability control:
         * `null` -> no reusability at all, `false`
         * anything else -> reusable.
         */
        return _reusableCancellableContinuation.value != null
    }

    /**
     * Awaits until previous call to `suspendCancellableCoroutineReusable` will
     * stop mutating cached instance
     */
    fun awaitReusability() {
        _reusableCancellableContinuation.loop {
            if (it !== REUSABLE_CLAIMED) return
        }
    }

    fun release() {
        /*
         * Called from `releaseInterceptedContinuation`, can be concurrent with
         * the code in `getResult` right after `trySuspend` returned `true`, so we have
         * to wait for a release here.
         */
        awaitReusability()
        reusableCancellableContinuation?.detachChild()
    }

    /**
     * Claims the continuation for [suspendCancellableCoroutineReusable] block,
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
                // potentially competing with cancel
                state is CancellableContinuationImpl<*> -> {
                    if (_reusableCancellableContinuation.compareAndSet(state, REUSABLE_CLAIMED)) {
                        return state as CancellableContinuationImpl<T>
                    }
                }
                state === REUSABLE_CLAIMED -> {
                    // Do nothing, wait until reusable instance will be returned from
                    // getResult() of a previous `suspendCancellableCoroutineReusable`
                }
                state is Throwable -> {
                    // Also do nothing, Throwable can only indicate that the CC
                    // is in REUSABLE_CLAIMED state, but with postponed cancellation
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
     * suspendCancellableCoroutineReusable { // <- claimed
     * // Any asynchronous cancellation is "postponed" while this block
     * // is being executed
     * } // postponed cancellation is checked here in `getResult`
     * ```
     *
     * See [CancellableContinuationImpl.getResult].
     */
    fun tryReleaseClaimedContinuation(continuation: CancellableContinuation<*>): Throwable? {
        _reusableCancellableContinuation.loop { state ->
            // not when(state) to avoid Intrinsics.equals call
            when {
                state === REUSABLE_CLAIMED -> {
                    if (_reusableCancellableContinuation.compareAndSet(REUSABLE_CLAIMED, continuation)) return null
                }
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
            resumeMode = MODE_ATOMIC
            dispatcher.dispatch(context, this)
        } else {
            executeUnconfined(state, MODE_ATOMIC) {
                withCoroutineContext(this.context, countOrElement) {
                    continuation.resumeWith(result)
                }
            }
        }
    }

    // We inline it to save an entry on the stack in cases where it shows (unconfined dispatcher)
    // It is used only in Continuation<T>.resumeCancellableWith
    @Suppress("NOTHING_TO_INLINE")
    inline fun resumeCancellableWith(
        result: Result<T>,
        noinline onCancellation: ((cause: Throwable) -> Unit)?
    ) {
        val state = result.toState(onCancellation)
        if (dispatcher.isDispatchNeeded(context)) {
            _state = state
            resumeMode = MODE_CANCELLABLE
            dispatcher.dispatch(context, this)
        } else {
            executeUnconfined(state, MODE_CANCELLABLE) {
                if (!resumeCancelled(state)) {
                    resumeUndispatchedWith(result)
                }
            }
        }
    }

    // takeState had already cleared the state so we cancel takenState here
    override fun cancelCompletedResult(takenState: Any?, cause: Throwable) {
        // It is Ok to call onCancellation here without try/catch around it, since this function only faces
        // a "bound" cancellation handler that performs the safe call to the user-specified code.
        if (takenState is CompletedWithCancellation) {
            takenState.onCancellation(cause)
        }
    }

    @Suppress("NOTHING_TO_INLINE")
    inline fun resumeCancelled(state: Any?): Boolean {
        val job = context[Job]
        if (job != null && !job.isActive) {
            val cause = job.getCancellationException()
            cancelCompletedResult(state, cause)
            resumeWithException(cause)
            return true
        }
        return false
    }

    @Suppress("NOTHING_TO_INLINE") // we need it inline to save us an entry on the stack
    inline fun resumeUndispatchedWith(result: Result<T>) {
        withContinuationContext(continuation, countOrElement) {
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
public fun <T> Continuation<T>.resumeCancellableWith(
    result: Result<T>,
    onCancellation: ((cause: Throwable) -> Unit)? = null
): Unit = when (this) {
    is DispatchedContinuation -> resumeCancellableWith(result, onCancellation)
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
    assert { mode != MODE_UNINITIALIZED } // invalid execution mode
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
