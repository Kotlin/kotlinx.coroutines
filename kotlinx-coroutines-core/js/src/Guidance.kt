package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext
import kotlin.js.Promise

/**
 * Deprecated version of [promise] that accepts a [Job].
 *
 * See the documentation for the non-deprecated [promise] function to learn about the functionality of this function.
 *
 * See the documentation for the deprecated [async] overload accepting a [Job] for an explanation of the reason
 * this pattern is deprecated and the list of possible alternatives.
 */
@Deprecated(
    "Passing a Job to coroutine builders breaks structured concurrency, leading to hard-to-diagnose errors. " +
        "This pattern should be avoided. " +
        "This overload will be deprecated with an error in the future.",
    level = DeprecationLevel.WARNING)
public fun <T> CoroutineScope.promise(
    context: Job,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): Promise<T> =
    promise(context as CoroutineContext, start, block)
