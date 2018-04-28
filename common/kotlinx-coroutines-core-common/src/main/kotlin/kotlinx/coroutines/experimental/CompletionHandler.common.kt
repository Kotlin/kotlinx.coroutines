/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.*

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
internal expect abstract class CompletionHandlerNode() : LockFreeLinkedListNode {
    val asHandler: CompletionHandler
    abstract fun invoke(cause: Throwable?)
}

// More compact version of CompletionHandlerNode for CancellableContinuation with same workaround for JS
internal expect abstract class CancellationHandler() {
    val asHandler: CompletionHandler
    abstract fun invoke(cause: Throwable?)
}

// :KLUDGE: We have to invoke a handler in platform-specific way via `invokeIt` extension,
// because we play type tricks on Kotlin/JS and handler is not necessarily a function there
internal expect fun CompletionHandler.invokeIt(cause: Throwable?)
