/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.intrinsics

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

/**
 * Use this function to restart coroutine directly from inside of [suspendCoroutine],
 * when the code is already in the context of this coroutine.
 * It does not use [ContinuationInterceptor] and does not update context of the current thread.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun <T> (suspend () -> T).startCoroutineUnintercepted(completion: Continuation<T>) {
    startDirect(completion) {
        startCoroutineUninterceptedOrReturn(completion)
    }
}

/**
 * Use this function to restart coroutine directly from inside of [suspendCoroutine],
 * when the code is already in the context of this coroutine.
 * It does not use [ContinuationInterceptor] and does not update context of the current thread.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun <R, T> (suspend (R) -> T).startCoroutineUnintercepted(receiver: R, completion: Continuation<T>) {
    startDirect(completion) {
        startCoroutineUninterceptedOrReturn(receiver, completion)
    }
}

/**
 * Use this function to start new coroutine in [CoroutineStart.UNDISPATCHED] mode &mdash;
 * immediately execute coroutine in the current thread until next suspension.
 * It does not use [ContinuationInterceptor], but updates the context of the current thread for the new coroutine.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun <T> (suspend () -> T).startCoroutineUndispatched(completion: Continuation<T>) {
    startDirect(completion) {
        withCoroutineContext(completion.context) {
            startCoroutineUninterceptedOrReturn(completion)
        }
    }
}

/**
 * Use this function to start new coroutine in [CoroutineStart.UNDISPATCHED] mode &mdash;
 * immediately execute coroutine in the current thread until next suspension.
 * It does not use [ContinuationInterceptor], but updates the context of the current thread for the new coroutine.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun <R, T> (suspend (R) -> T).startCoroutineUndispatched(receiver: R, completion: Continuation<T>) {
    startDirect(completion) {
        withCoroutineContext(completion.context) {
            startCoroutineUninterceptedOrReturn(receiver, completion)
        }
    }
}

private inline fun <T> startDirect(completion: Continuation<T>, block: () -> Any?) {
    val value = try {
        block()
    } catch (e: Throwable) {
        completion.resumeWithException(e)
        return
    }
    if (value !== COROUTINE_SUSPENDED) {
        @Suppress("UNCHECKED_CAST")
        completion.resume(value as T)
    }
}

/**
 * Starts this coroutine with the given code [block] in the same context and returns result when it
 * completes without suspension.
 * This function shall be invoked at most once on this coroutine.
 *
 * First, this function initializes parent job from the `parentContext` of this coroutine that was passed to it
 * during construction. Second, it starts the coroutine using [startCoroutineUninterceptedOrReturn].
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun <T> AbstractCoroutine<T>.startUndispatchedOrReturn(block: suspend () -> T): Any? {
    initParentJob()
    return undispatchedResult { block.startCoroutineUninterceptedOrReturn(this) }
}

/**
 * Starts this coroutine with the given code [block] in the same context and returns result when it
 * completes without suspension.
 * This function shall be invoked at most once on this coroutine.
 *
 * First, this function initializes parent job from the `parentContext` of this coroutine that was passed to it
 * during construction. Second, it starts the coroutine using [startCoroutineUninterceptedOrReturn].
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun <T, R> AbstractCoroutine<T>.startUndispatchedOrReturn(receiver: R, block: suspend R.() -> T): Any? {
    initParentJob()
    return undispatchedResult { block.startCoroutineUninterceptedOrReturn(receiver, this) }
}

private inline fun <T> AbstractCoroutine<T>.undispatchedResult(startBlock: () -> Any?): Any? {
    val result = try {
        startBlock()
    } catch (e: Throwable) {
        CompletedExceptionally(e)
    }
    return when {
        result === COROUTINE_SUSPENDED -> COROUTINE_SUSPENDED
        makeCompletingOnce(result, MODE_IGNORE) -> {
            if (result is CompletedExceptionally) throw result.cause else result
        }
        else -> COROUTINE_SUSPENDED
    }
}