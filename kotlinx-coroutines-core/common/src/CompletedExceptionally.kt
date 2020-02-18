/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

internal fun <T> Result<T>.toState(): Any? = fold({ it }, { CompletedExceptionally(it) })

internal fun <T> Result<T>.toState(caller: CancellableContinuation<*>): Any? = fold({ it },
    { CompletedExceptionally(recoverStackTrace(it, caller)) })

@Suppress("RESULT_CLASS_IN_RETURN_TYPE", "UNCHECKED_CAST")
internal fun <T> recoverResult(state: Any?, uCont: Continuation<T>): Result<T> =
    if (state is CompletedExceptionally)
        Result.failure(recoverStackTrace(state.cause, uCont))
    else
        Result.success(state as T)

/**
 * Class for an internal state of a job that was cancelled (completed exceptionally).
 *
 * @param cause the exceptional completion cause. It's either original exceptional cause
 *        or artificial [CancellationException] if no cause was provided
 */
internal open class CompletedExceptionally(
    @JvmField public val cause: Throwable,
    handled: Boolean = false
) {
    private val _handled = atomic(handled)
    val handled: Boolean get() = _handled.value
    fun makeHandled(): Boolean = _handled.compareAndSet(false, true)
    override fun toString(): String = "$classSimpleName[$cause]"
}

/**
 * A specific subclass of [CompletedExceptionally] for cancelled [AbstractContinuation].
 *
 * @param continuation the continuation that was cancelled.
 * @param cause the exceptional completion cause. If `cause` is null, then a [CancellationException]
 *        if created on first access to [exception] property.
 */
internal class CancelledContinuation(
    continuation: Continuation<*>,
    cause: Throwable?,
    handled: Boolean
) : CompletedExceptionally(cause ?: CancellationException("Continuation $continuation was cancelled normally"), handled) {
    private val _resumed = atomic(false)
    fun makeResumed(): Boolean = _resumed.compareAndSet(false, true)
}
