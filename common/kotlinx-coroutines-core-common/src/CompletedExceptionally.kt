/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
public fun <T> SuccessOrFailure<T>.toState(): Any? =
    if (isSuccess) getOrThrow() else CompletedExceptionally(exceptionOrNull()!!) // todo: need to do it better

/**
 * Class for an internal state of a job that had completed exceptionally, including cancellation.
 *
 * **Note: This class cannot be used outside of internal coroutines framework**.
 * **Note: cannot be internal until we get rid of MutableDelegateContinuation in IO**
 *
 * @param cause the exceptional completion cause. It's either original exceptional cause
 *        or artificial JobCancellationException if no cause was provided
 * @suppress **This is unstable API and it is subject to change.**
 */
open class CompletedExceptionally(
    @JvmField public val cause: Throwable
) {
    override fun toString(): String = "$classSimpleName[$cause]"
}

/**
 * A specific subclass of [CompletedExceptionally] for cancelled jobs.
 *
 * **Note: This class cannot be used outside of internal coroutines framework**.
 *
 * @param job the job that was cancelled.
 * @param cause the exceptional completion cause. If `cause` is null, then a [JobCancellationException] is created.
 * @suppress **This is unstable API and it is subject to change.**
 */
internal class Cancelled(
    job: Job,
    cause: Throwable?
) : CompletedExceptionally(cause ?: JobCancellationException("Job was cancelled normally", null, job))

/**
 * A specific subclass of [CompletedExceptionally] for cancelled [AbstractContinuation].
 *
 * **Note: This class cannot be used outside of internal coroutines framework**.
 *
 * @param continuation the continuation that was cancelled.
 * @param cause the exceptional completion cause. If `cause` is null, then a [JobCancellationException]
 *        if created on first get from [exception] property.
 * @suppress **This is unstable API and it is subject to change.**
 */
public class CancelledContinuation(
    continuation: Continuation<*>,
    cause: Throwable?
) : CompletedExceptionally(cause ?: CancellationException("Continuation $continuation was cancelled normally"))
