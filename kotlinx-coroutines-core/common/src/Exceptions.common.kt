package kotlinx.coroutines

/**
 * This exception gets thrown if an exception is caught while processing [InternalCompletionHandler] invocation for [Job].
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public class CompletionHandlerException(message: String, cause: Throwable) : RuntimeException(message, cause)

public expect open class CancellationException(message: String?) : IllegalStateException

public expect fun CancellationException(message: String?, cause: Throwable?) : CancellationException

internal expect class JobCancellationException(
    message: String,
    cause: Throwable?,
    job: Job
) : CancellationException {
    internal val job: Job
}

internal class CoroutinesInternalError(message: String, cause: Throwable) : Error(message, cause)

// For use in tests
internal expect val RECOVER_STACK_TRACES: Boolean
