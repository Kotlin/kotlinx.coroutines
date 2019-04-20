/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public expect class CompletionHandlerException(message: String, cause: Throwable) : RuntimeException

public expect open class CancellationException(message: String?) : IllegalStateException

@Suppress("FunctionName")
public expect fun CancellationException(message: String?, cause: Throwable?) : CancellationException

internal expect class JobCancellationException(
    message: String,
    cause: Throwable?,
    job: Job
) : CancellationException {
    internal val job: Job
}

internal expect class CoroutinesInternalError(message: String, cause: Throwable) : Error

internal expect fun Throwable.addSuppressedThrowable(other: Throwable)
// For use in tests
internal expect val RECOVER_STACK_TRACES: Boolean