package kotlinx.coroutines

/**
 * Handler for [Job.invokeOnCompletion] and [CancellableContinuation.invokeOnCancellation].
 *
 * Installed handler should not throw any exceptions. If it does, they will get caught,
 * wrapped into [CompletionHandlerException], and rethrown, potentially causing crash of unrelated code.
 *
 * The meaning of `cause` that is passed to the handler:
 * - Cause is `null` when the job has completed normally.
 * - Cause is an instance of [CancellationException] when the job was cancelled _normally_.
 *   **It should not be treated as an error**. In particular, it should not be reported to error logs.
 * - Otherwise, the job had _failed_.
 *
 * **Note**: This type is a part of internal machinery that supports parent-child hierarchies
 * and allows for implementation of suspending functions that wait on the Job's state.
 * This type should not be used in general application code.
 * Implementations of `CompletionHandler` must be fast and _lock-free_.
 */
public typealias CompletionHandler = (cause: Throwable?) -> Unit

@InternalCoroutinesApi
public fun interface InternalCompletionHandler {
    public fun invoke(cause: Throwable?)

    public class UserSupplied(
        private val handler: (cause: Throwable?) -> Unit
    ) : InternalCompletionHandler {
        override fun invoke(cause: Throwable?) {
            handler(cause)
        }
    }
}

internal inline fun <reified T> InternalCompletionHandler.isHandlerOf(): Boolean = this is T
