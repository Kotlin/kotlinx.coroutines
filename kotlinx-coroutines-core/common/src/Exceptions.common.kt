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
public class CompletionHandlerException(message: String, cause: Throwable) : RuntimeException(message, cause)

public expect open class CancellationException(message: String?) : IllegalStateException

@Suppress("FunctionName", "NO_ACTUAL_FOR_EXPECT")
public expect fun CancellationException(message: String?, cause: Throwable?) : CancellationException

internal expect class JobCancellationException(
    message: String,
    cause: Throwable?,
    job: Job
) : CancellationException {
    internal val job: Job
}

internal class CoroutinesInternalError(message: String, cause: Throwable) : Error(message, cause)

internal expect fun Throwable.addSuppressedThrowable(other: Throwable)
// For use in tests
internal expect val RECOVER_STACK_TRACES: Boolean