/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * This exception gets thrown if an exception is caught while processing [CompletionHandler] invocation for [Job].
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public actual class CompletionHandlerException public actual constructor(
    message: String,
    public override val cause: Throwable
) : RuntimeException(message.withCause(cause))

/**
 * Thrown by cancellable suspending functions if the [Job] of the coroutine is cancelled while it is suspending.
 * It indicates _normal_ cancellation of a coroutine.
 * **It is not printed to console/log by default uncaught exception handler**.
 * (see [CoroutineExceptionHandler]).
 */
public actual open class CancellationException actual constructor(message: String?) : IllegalStateException(message)

/**
 * Thrown by cancellable suspending functions if the [Job] of the coroutine is cancelled or completed
 * without cause, or with a cause or exception that is not [CancellationException]
 * (see [Job.getCancellationException]).
 */
internal actual class JobCancellationException public actual constructor(
    message: String,
    public override val cause: Throwable?,
    internal actual val job: Job
) : CancellationException(message.withCause(cause)) {
    override fun toString(): String = "${super.toString()}; job=$job"
    override fun equals(other: Any?): Boolean =
        other === this ||
            other is JobCancellationException && other.message == message && other.job == job && other.cause == cause
    override fun hashCode(): Int =
        (message!!.hashCode() * 31 + job.hashCode()) * 31 + (cause?.hashCode() ?: 0)
}

internal actual class DispatchException actual constructor(message: String, cause: Throwable) : RuntimeException(message.withCause(cause))

@Suppress("FunctionName")
internal fun IllegalStateException(message: String, cause: Throwable?) =
    IllegalStateException(message.withCause(cause))

private fun String.withCause(cause: Throwable?) =
    if (cause == null) this else "$this; caused by $cause"

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun Throwable.addSuppressedThrowable(other: Throwable) { /* empty */ }
