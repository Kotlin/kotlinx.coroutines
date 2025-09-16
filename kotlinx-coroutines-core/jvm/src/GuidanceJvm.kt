package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext

/**
 * Deprecated version of [runInterruptible] that accepts a [Job].
 *
 * The purpose of the [runInterruptible] function is to interrupt the code executing in [block]
 * when the caller gets cancelled, but passing a [Job] in [context] breaks the structured concurrency relationship
 * between the code being invoked and the code running in [block].
 *
 * See the [withContext] documentation for a description of how to ensure the [block] gets cancelled when a non-caller
 * [Job] gets cancelled.
 */
@Deprecated(
    "Passing a Job to `runInterruptible` prevents it from being cancelled when the caller gets cancelled. " +
        "This pattern should be avoided. " +
        "This overload will be deprecated with an error in the future.",
    level = DeprecationLevel.WARNING)
public suspend fun <T> runInterruptible(
    context: Job,
    block: () -> T
): T = runInterruptible(context as CoroutineContext, block)
