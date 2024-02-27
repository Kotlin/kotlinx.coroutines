package kotlinx.coroutines

/**
 * Handler for [Job.invokeOnCompletion] and [CancellableContinuation.invokeOnCancellation].
 *
 * The meaning of `cause` that is passed to the handler is:
 * - It is `null` if the job has completed normally or the continuation was cancelled without a `cause`.
 * - It is an instance of [CancellationException] if the job or the continuation was cancelled _normally_.
 *   **It should not be treated as an error**. In particular, it should not be reported to error logs.
 * - Otherwise, the job or the continuation had _failed_.
 *
 * A function used for this should not throw any exceptions.
 * If it does, they will get caught, wrapped into [CompletionHandlerException], and then either
 * - passed to [handleCoroutineException] for [CancellableContinuation.invokeOnCancellation]
 *   and, for [Job] instances that are coroutines, [Job.invokeOnCompletion], or
 * - for [Job] instances that are not coroutines, simply thrown, potentially crashing unrelated code.
 *
 * Functions used for this must be fast, non-blocking, and thread-safe.
 * This handler can be invoked concurrently with the surrounding code.
 * There is no guarantee on the execution context in which the function is invoked.
 *
 * **Note**: This type is a part of internal machinery that supports parent-child hierarchies
 * and allows for implementation of suspending functions that wait on the Job's state.
 * This type should not be used in general application code.
 */
// TODO: deprecate. This doesn't seem better than a simple function type.
public typealias CompletionHandler = (cause: Throwable?) -> Unit

/**
 * Essentially the same as just a function from `Throwable?` to `Unit`.
 * The only thing implementors can do is call [invoke].
 * The reason this abstraction exists is to allow providing a readable [toString] in the list of completion handlers
 * as seen from the debugger.
 * Use [UserSupplied] to create an instance from a lambda.
 * We can't avoid defining a separate type, because on JS, you can't inherit from a function type.
 *
 * @see CancelHandler for a very similar interface, but used for handling cancellation and not completion.
 */
internal interface InternalCompletionHandler {
    /**
     * Signals completion.
     *
     * This function:
     * - Does not throw any exceptions.
     *   For [Job] instances that are coroutines, exceptions thrown by this function will be caught, wrapped into
     *   [CompletionHandlerException], and passed to [handleCoroutineException], but for those that are not coroutines,
     *   they will just be rethrown, potentially crashing unrelated code.
     * - Is fast, non-blocking, and thread-safe.
     * - Can be invoked concurrently with the surrounding code.
     * - Can be invoked from any context.
     *
     * The meaning of `cause` that is passed to the handler is:
     * - It is `null` if the job has completed normally.
     * - It is an instance of [CancellationException] if the job was cancelled _normally_.
     *   **It should not be treated as an error**. In particular, it should not be reported to error logs.
     * - Otherwise, the job had _failed_.
     */
    fun invoke(cause: Throwable?)

    /**
     * A lambda passed from outside the coroutine machinery.
     *
     * See the requirements for [InternalCompletionHandler.invoke] when implementing this function.
     */
    class UserSupplied(private val handler: (cause: Throwable?) -> Unit) : InternalCompletionHandler {
        /** @suppress */
        override fun invoke(cause: Throwable?) { handler(cause) }

        override fun toString() = "InternalCompletionHandler.UserSupplied[${handler.classSimpleName}@$hexAddress]"
    }
}
