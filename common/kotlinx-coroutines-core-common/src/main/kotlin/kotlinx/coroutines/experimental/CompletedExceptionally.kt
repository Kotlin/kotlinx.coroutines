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

import kotlinx.coroutines.experimental.internalAnnotations.*
import kotlin.coroutines.experimental.*

/**
 * Class for an internal state of a job that had completed exceptionally, including cancellation.
 *
 * **Note: This class cannot be used outside of internal coroutines framework**.
 * **Note: cannot be internal until we get rid of MutableDelegateContinuation in IO**
 *
 * @param cause the exceptional completion cause. It's either original exceptional cause
 *        or artificial JobCancellationException if no cause was provided
 * @suppress **This is unstable API and it is subject to change.**
 */
open class CompletedExceptionally(
    @JvmField public val cause: Throwable
) {
    override fun toString(): String = "$classSimpleName[$cause]"
}

/**
 * A specific subclass of [CompletedExceptionally] for cancelled jobs.
 *
 * **Note: This class cannot be used outside of internal coroutines framework**.
 * TODO rename to CancelledJob?
 *
 * @param job the job that was cancelled.
 * @param cause the exceptional completion cause. If `cause` is null, then a [JobCancellationException] is created.
 * @suppress **This is unstable API and it is subject to change.**
 */
internal class Cancelled(
    job: Job,
    cause: Throwable?
) : CompletedExceptionally(cause ?: JobCancellationException("Job was cancelled normally", null, job))

/**
 * A specific subclass of [CompletedExceptionally] for cancelled [AbstractContinuation].
 *
 * **Note: This class cannot be used outside of internal coroutines framework**.
 *
 * @param continuation the continuation that was cancelled.
 * @param cause the exceptional completion cause. If `cause` is null, then a [JobCancellationException]
 *        if created on first get from [exception] property.
 * @suppress **This is unstable API and it is subject to change.**
 */
public class CancelledContinuation(
    continuation: Continuation<*>,
    cause: Throwable?
) : CompletedExceptionally(cause ?: CancellationException("Continuation $continuation was cancelled normally"))
