/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

@PublishedApi internal const val MODE_ATOMIC_DEFAULT = 0 // schedule non-cancellable dispatch for suspendCoroutine
@PublishedApi internal const val MODE_CANCELLABLE = 1    // schedule cancellable dispatch for suspendCancellableCoroutine
@PublishedApi internal const val MODE_DIRECT = 2         // when the context is right just invoke the delegate continuation direct
@PublishedApi internal const val MODE_UNDISPATCHED = 3   // when the thread is right, but need to mark it with current coroutine
@PublishedApi internal const val MODE_IGNORE = 4         // don't do anything

internal val Int.isCancellableMode get() = this == MODE_CANCELLABLE
internal val Int.isDispatchedMode get() = this == MODE_ATOMIC_DEFAULT || this == MODE_CANCELLABLE

internal fun <T> Continuation<T>.resumeMode(value: T, mode: Int) {
    when (mode) {
        MODE_ATOMIC_DEFAULT -> resume(value)
        MODE_CANCELLABLE -> resumeCancellable(value)
        MODE_DIRECT -> resumeDirect(value)
        MODE_UNDISPATCHED -> (this as DispatchedContinuation).resumeUndispatched(value)
        MODE_IGNORE -> {}
        else -> error("Invalid mode $mode")
    }
}

internal fun <T> Continuation<T>.resumeWithExceptionMode(exception: Throwable, mode: Int) {
    when (mode) {
        MODE_ATOMIC_DEFAULT -> resumeWithException(exception)
        MODE_CANCELLABLE -> resumeCancellableWithException(exception)
        MODE_DIRECT -> resumeDirectWithException(exception)
        MODE_UNDISPATCHED -> (this as DispatchedContinuation).resumeUndispatchedWithException(exception)
        MODE_IGNORE -> {}
        else -> error("Invalid mode $mode")
    }
}

internal fun <T> Continuation<T>.resumeUninterceptedMode(value: T, mode: Int) {
    when (mode) {
        MODE_ATOMIC_DEFAULT -> intercepted().resume(value)
        MODE_CANCELLABLE -> intercepted().resumeCancellable(value)
        MODE_DIRECT -> resume(value)
        MODE_UNDISPATCHED -> withCoroutineContext(context) { resume(value) }
        MODE_IGNORE -> {}
        else -> error("Invalid mode $mode")
    }
}

internal fun <T> Continuation<T>.resumeUninterceptedWithExceptionMode(exception: Throwable, mode: Int) {
    when (mode) {
        MODE_ATOMIC_DEFAULT -> intercepted().resumeWithException(exception)
        MODE_CANCELLABLE -> intercepted().resumeCancellableWithException(exception)
        MODE_DIRECT -> resumeWithException(exception)
        MODE_UNDISPATCHED -> withCoroutineContext(context) { resumeWithException(exception) }
        MODE_IGNORE -> {}
        else -> error("Invalid mode $mode")
    }
}
