/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("FunctionName")

package kotlinx.coroutines

/**
 * Thrown by cancellable suspending functions if the [Job] of the coroutine is cancelled while it is suspending.
 * It indicates _normal_ cancellation of a coroutine.
 * **It is not printed to console/log by default uncaught exception handler**.
 * See [CoroutineExceptionHandler]
*/
public actual typealias CancellationException = java.util.concurrent.CancellationException

/**
 * Creates a cancellation exception with a specified message and [cause].
 */
@Suppress("FunctionName")
public actual fun CancellationException(message: String?, cause: Throwable?) : CancellationException =
    CancellationException(message).apply { initCause(cause) }

/**
 * Thrown by cancellable suspending functions if the [Job] of the coroutine is cancelled or completed
 * without cause, or with a cause or exception that is not [CancellationException]
 * (see [Job.getCancellationException]).
 */
internal actual class JobCancellationException public actual constructor(
    message: String,
    cause: Throwable?,
    @JvmField internal actual val job: Job
) : CancellationException(message), CopyableThrowable<JobCancellationException> {

    init {
        if (cause != null) initCause(cause)
    }

    override fun fillInStackTrace(): Throwable {
        if (DEBUG) {
            return super.fillInStackTrace()
        }
        // Prevent Android <= 6.0 bug, #1866
        stackTrace = emptyArray()
        /*
         * In non-debug mode we don't want to have a stacktrace on every cancellation/close,
         * parent job reference is enough. Stacktrace of JCE is not needed most of the time (e.g., it is not logged)
         * and hurts performance.
         */
        return this
    }

    override fun createCopy(): JobCancellationException? {
        if (DEBUG) {
            return JobCancellationException(message!!, this, job)
        }

        /*
         * In non-debug mode we don't copy JCE for speed as it does not have the stack trace anyway.
         */
        return null
    }

    override fun toString(): String = "${super.toString()}; job=$job"

    override fun equals(other: Any?): Boolean =
        other === this ||
            other is JobCancellationException && other.message == message && other.job == job && other.cause == cause
    override fun hashCode(): Int =
        (message!!.hashCode() * 31 + job.hashCode()) * 31 + (cause?.hashCode() ?: 0)
}

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun Throwable.addSuppressedThrowable(other: Throwable) =
    addSuppressed(other)
