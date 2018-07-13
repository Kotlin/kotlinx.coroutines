/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*

/**
 * Handler for [Job.invokeOnCompletion] and [CancellableContinuation.invokeOnCancellation].
 *
 * Installed handler should not throw any exceptions. If it does, they will get caught,
 * wrapped into [CompletionHandlerException], and rethrown, potentially causing crash of unrelated code.
 *
 * The meaning of `cause` that is passed to the handler:
 * * Cause is `null` when job has completed normally.
 * * Cause is an instance of [CancellationException] when job was cancelled _normally_.
 *   **It should not be treated as an error**. In particular, it should not be reported to error logs.
 * * Otherwise, the job had _failed_.
 *
 * **Note**: This type is a part of internal machinery that supports parent-child hierarchies
 * and allows for implementation of suspending functions that wait on the Job's state.
 * This type should not be used in general application code.
 * Implementations of `CompletionHandler` must be fast and _lock-free_.
 */
public typealias CompletionHandler = (cause: Throwable?) -> Unit

// We want class that extends LockFreeLinkedListNode & CompletionHandler but we cannot do it on Kotlin/JS,
// so this expect class provides us with the corresponding abstraction in a platform-agnostic way.
internal expect abstract class CompletionHandlerBase() : LockFreeLinkedListNode {
    abstract fun invoke(cause: Throwable?)
}

internal expect val CompletionHandlerBase.asHandler: CompletionHandler

// More compact version of CompletionHandlerBase for CancellableContinuation with same workaround for JS
internal expect abstract class CancelHandlerBase() {
    abstract fun invoke(cause: Throwable?)
}

internal expect val CancelHandlerBase.asHandler: CompletionHandler

// :KLUDGE: We have to invoke a handler in platform-specific way via `invokeIt` extension,
// because we play type tricks on Kotlin/JS and handler is not necessarily a function there
internal expect fun CompletionHandler.invokeIt(cause: Throwable?)
