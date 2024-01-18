package kotlinx.coroutines

/**
 * Thrown by cancellable suspending functions if the [Job] of the coroutine is cancelled while it is suspending.
 * It indicates _normal_ cancellation of a coroutine.
 * **It is not printed to console/log by default uncaught exception handler**.
 * (see [CoroutineExceptionHandler]).
 */
public actual typealias CancellationException = kotlin.coroutines.cancellation.CancellationException

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
@kotlin.internal.LowPriorityInOverloadResolution
public actual fun CancellationException(message: String?, cause: Throwable?): CancellationException =
    CancellationException(message, cause)

/**
 * Thrown by cancellable suspending functions if the [Job] of the coroutine is cancelled or completed
 * without cause, or with a cause or exception that is not [CancellationException]
 * (see [Job.getCancellationException]).
 */
internal actual class JobCancellationException public actual constructor(
    message: String,
    cause: Throwable?,
    internal actual val job: Job
) : CancellationException(message, cause) {
    override fun toString(): String = "${super.toString()}; job=$job"
    override fun equals(other: Any?): Boolean =
        other === this ||
            other is JobCancellationException && other.message == message && other.job == job && other.cause == cause
    override fun hashCode(): Int =
        (message!!.hashCode() * 31 + job.hashCode()) * 31 + (cause?.hashCode() ?: 0)
}

// For use in tests
internal actual val RECOVER_STACK_TRACES: Boolean = false
