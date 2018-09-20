/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("JobKt")

package kotlinx.coroutines.experimental

import java.util.concurrent.*

/**
 * Cancels a specified [future] when this job is cancelled.
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCompletion { future.cancel(false) }
 * ```
 * 
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun Job.cancelFutureOnCompletion(future: Future<*>): DisposableHandle =
    invokeOnCompletion(handler = CancelFutureOnCompletion(this, future)) // TODO make it work only on cancellation as well?

/**
 * Cancels a specified [future] when this job is cancelled.
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCompletion { future.cancel(false) }
 * ```
 */
@Deprecated(
    message = "Disposable handlers on regular completion are no longer supported",
    replaceWith = ReplaceWith("cancelFutureOnCancellation(future)"),
    level = DeprecationLevel.WARNING)
public fun CancellableContinuation<*>.cancelFutureOnCompletion(future: Future<*>): DisposableHandle {
    cancelFutureOnCancellation(future)
    return NonDisposableHandle
}

/**
 * Cancels a specified [future] when this job is cancelled.
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCancellation { future.cancel(false) }
 * ```
 */
public fun CancellableContinuation<*>.cancelFutureOnCancellation(future: Future<*>) =
    invokeOnCancellation(handler = CancelFutureOnCancel(future))

private class CancelFutureOnCompletion(
    job: Job,
    private val future: Future<*>
) : JobNode<Job>(job)  {
    override fun invoke(cause: Throwable?) {
        // Don't interrupt when cancelling future on completion, because no one is going to reset this
        // interruption flag and it will cause spurious failures elsewhere
        future.cancel(false)
    }
    override fun toString() = "CancelFutureOnCompletion[$future]"
}

private class CancelFutureOnCancel(private val future: Future<*>) : CancelHandler()  {
    override fun invoke(cause: Throwable?) {
        // Don't interrupt when cancelling future on completion, because no one is going to reset this
        // interruption flag and it will cause spurious failures elsewhere
        future.cancel(false)
    }
    override fun toString() = "CancelFutureOnCancel[$future]"
}
