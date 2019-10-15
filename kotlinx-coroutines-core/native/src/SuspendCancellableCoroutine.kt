/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.disposeContinuation
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

public actual suspend inline fun <T> suspendCancellableCoroutine(
    crossinline block: (CancellableContinuation<T>) -> Unit
): T =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val cancellable = CancellableContinuationImpl(uCont.intercepted(), resumeMode = MODE_CANCELLABLE)
        try {
            block(cancellable)
            cancellable.getResult()
        } catch (e: Throwable) {
            disposeContinuation { cancellable.delegate }
            throw e
        }
    }

@InternalCoroutinesApi
public actual suspend inline fun <T> suspendAtomicCancellableCoroutine(
    crossinline block: (CancellableContinuation<T>) -> Unit
): T =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val cancellable = CancellableContinuationImpl(uCont.intercepted(), resumeMode = MODE_ATOMIC_DEFAULT)
        try {
            block(cancellable)
            cancellable.getResult()
        } catch (e: Throwable) {
            disposeContinuation { cancellable.delegate }
            throw e
        }
    }

internal actual suspend inline fun <T> suspendAtomicCancellableCoroutineReusable(
    crossinline block: (CancellableContinuation<T>) -> Unit
): T {
    // todo: Reuse is not support on Kotlin/Native due to platform peculiarities making it had to properly
    // split DispatchedContinuation / CancellableContinuationImpl state across workers.
    // If used outside of our dispatcher
    return suspendAtomicCancellableCoroutine(block)
}

