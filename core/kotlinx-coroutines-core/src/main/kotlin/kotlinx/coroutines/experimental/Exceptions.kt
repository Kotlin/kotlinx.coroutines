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

import java.util.concurrent.*

/**
 * This exception gets thrown if an exception is caught while processing [CompletionHandler] invocation for [Job].
 */
public actual class CompletionHandlerException actual constructor(
    message: String,
    cause: Throwable
) : RuntimeException(message, cause)

/**
 * Thrown by cancellable suspending functions if the [Job] of the coroutine is cancelled while it is suspending.
 * It indicates _normal_ cancellation of a coroutine.
 * **It is not printed to console/log by default uncaught exception handler**.
 * (see [handleCoroutineException]).
*/
public actual typealias CancellationException = java.util.concurrent.CancellationException

/**
 * Thrown by cancellable suspending functions if the [Job] of the coroutine is cancelled or completed
 * without cause, or with a cause or exception that is not [CancellationException]
 * (see [Job.getCancellationException]).
 */
public actual class JobCancellationException public actual constructor(
    message: String,
    cause: Throwable?,
    /**
     * The job that was cancelled.
     */
    public actual val job: Job
) : CancellationException(message) {
    init { if (cause != null) initCause(cause) }
    override fun toString(): String = "${super.toString()}; job=$job"
    override fun equals(other: Any?): Boolean =
        other === this ||
            other is JobCancellationException && other.message == message && other.job == job && other.cause == cause
    override fun hashCode(): Int =
        (message!!.hashCode() * 31 + job.hashCode()) * 31 + (cause?.hashCode() ?: 0)
}

internal actual class DispatchException actual constructor(message: String, cause: Throwable) : RuntimeException(message, cause)

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun Throwable.addSuppressedThrowable(other: Throwable) =
    addSuppressed(other)
