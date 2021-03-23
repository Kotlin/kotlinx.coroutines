/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.intrinsics

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * Use this function to restart a coroutine directly from inside of [suspendCoroutine],
 * when the code is already in the context of this coroutine.
 * It does not use [ContinuationInterceptor] and does not update the context of the current thread.
 */
internal fun <T> (suspend () -> T).startCoroutineUnintercepted(completion: Continuation<T>) {
    startDirect(completion) { actualCompletion ->
        startCoroutineUninterceptedOrReturn(actualCompletion)
    }
}

/**
 * Use this function to restart a coroutine directly from inside of [suspendCoroutine],
 * when the code is already in the context of this coroutine.
 * It does not use [ContinuationInterceptor] and does not update the context of the current thread.
 */
internal fun <R, T> (suspend (R) -> T).startCoroutineUnintercepted(receiver: R, completion: Continuation<T>) {
    startDirect(completion) {  actualCompletion ->
        startCoroutineUninterceptedOrReturn(receiver, actualCompletion)
    }
}

/**
 * Use this function to start a new coroutine in [CoroutineStart.UNDISPATCHED] mode &mdash;
 * immediately execute the coroutine in the current thread until the next suspension.
 * It does not use [ContinuationInterceptor], but updates the context of the current thread for the new coroutine.
 */
internal fun <T> (suspend () -> T).startCoroutineUndispatched(completion: Continuation<T>) {
    startDirect(completion) { actualCompletion ->
        withCoroutineContext(completion.context, null) {
            startCoroutineUninterceptedOrReturn(actualCompletion)
        }
    }
}

/**
 * Use this function to start a new coroutine in [CoroutineStart.UNDISPATCHED] mode &mdash;
 * immediately execute the coroutine in the current thread until the next suspension.
 * It does not use [ContinuationInterceptor], but updates the context of the current thread for the new coroutine.
 */
internal fun <R, T> (suspend (R) -> T).startCoroutineUndispatched(receiver: R, completion: Continuation<T>) {
    startDirect(completion) { actualCompletion ->
        withCoroutineContext(completion.context, null) {
            startCoroutineUninterceptedOrReturn(receiver, actualCompletion)
        }
    }
}

/**
 * Starts the given [block] immediately in the current stack-frame until the first suspension point.
 * This method supports debug probes and thus can intercept completion, thus completion is provided
 * as the parameter of [block].
 */
private inline fun <T> startDirect(completion: Continuation<T>, block: (Continuation<T>) -> Any?) {
    val actualCompletion = probeCoroutineCreated(completion)
    val value = try {
        block(actualCompletion)
    } catch (e: Throwable) {
        actualCompletion.resumeWithException(e)
        return
    }
    if (value !== COROUTINE_SUSPENDED) {
        @Suppress("UNCHECKED_CAST")
        actualCompletion.resume(value as T)
    }
}

/**
 * Starts this coroutine with the given code [block] in the same context and returns the coroutine result when it
 * completes without suspension.
 * This function shall be invoked at most once on this coroutine.
 * This function checks cancellation of the outer [Job] on fast-path.
 *
 * It starts the coroutine using [startCoroutineUninterceptedOrReturn].
 */
internal fun <T, R> ScopeCoroutine<T>.startUndispatchedOrReturn(receiver: R, block: suspend R.() -> T): Any? {
    return undispatchedResult({ true }) {
        block.startCoroutineUninterceptedOrReturn(receiver, this)
    }
}

/**
 * Same as [startUndispatchedOrReturn], but ignores [TimeoutCancellationException] on fast-path.
 */
internal fun <T, R> ScopeCoroutine<T>.startUndispatchedOrReturnIgnoreTimeout(
    receiver: R, block: suspend R.() -> T
): Any? {
    return undispatchedResult({ e -> !(e is TimeoutCancellationException && e.coroutine === this) }) {
        block.startCoroutineUninterceptedOrReturn(receiver, this)
    }
}

private inline fun <T> ScopeCoroutine<T>.undispatchedResult(
    shouldThrow: (Throwable) -> Boolean,
    startBlock: () -> Any?
): Any? {
    val result = try {
        startBlock()
    } catch (e: Throwable) {
        CompletedExceptionally(e)
    }
    /*
     * We're trying to complete our undispatched block here and have three code-paths:
     * (1) Coroutine is suspended.
     * Otherwise, coroutine had returned result, so we are completing our block (and its job).
     * (2) If we can't complete it or started waiting for children, we suspend.
     * (3) If we have successfully completed the coroutine state machine here,
     *     then we take the actual final state of the coroutine from makeCompletingOnce and return it.
     *
     * shouldThrow parameter is a special code path for timeout coroutine:
     * If timeout is exceeded, but withTimeout() block was not suspended, we would like to return block value,
     * not a timeout exception.
     */
    if (result === COROUTINE_SUSPENDED) return COROUTINE_SUSPENDED // (1)
    val state = makeCompletingOnce(result)
    if (state === COMPLETING_WAITING_CHILDREN) return COROUTINE_SUSPENDED // (2)
    return if (state is CompletedExceptionally) { // (3)
        when {
            shouldThrow(state.cause) -> throw recoverStackTrace(state.cause, uCont)
            result is CompletedExceptionally -> throw recoverStackTrace(result.cause, uCont)
            else -> result
        }
    } else {
        state.unboxState()
    }
}
