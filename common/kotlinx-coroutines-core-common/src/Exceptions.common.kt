/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

@InternalCoroutinesApi
public expect class CompletionHandlerException(message: String, cause: Throwable) : RuntimeException

public expect open class CancellationException(message: String?) : IllegalStateException

/**
 * @suppress **Deprecated**: Replace with [CancellationException].
 */
@InternalCoroutinesApi
@Deprecated( // todo: remove deprecated, make it internal
    message = "Replace with CancellationException",
    replaceWith = ReplaceWith("CancellationException"))
public expect class JobCancellationException(
    message: String,
    cause: Throwable?,
    job: Job
) : CancellationException {
    internal val job: Job
}

internal expect class DispatchException(message: String, cause: Throwable) : RuntimeException

internal expect fun Throwable.addSuppressedThrowable(other: Throwable)