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

/**
 * Class for an internal state of a job that had completed exceptionally, including cancellation.
 *
 * **Note: This class cannot be used outside of internal coroutines framework**.
 *
 * @param cause the exceptional completion cause. It's either original exceptional cause
 *        or artificial JobCancellationException if no cause was provided
 * @suppress **This is unstable API and it is subject to change.**
 */
public open class CompletedExceptionally(public val cause: Throwable) {

    /**
     * Returns completion exception.
     */
    public val exception: Throwable get() = cause // alias for backward compatibility

    /**
     * Returns true if the current exceptional reason is cancellation without cause
     */
    open fun isCancelledWithoutCause() = false

    override fun toString(): String = "$classSimpleName[$exception]"
}

/**
 * A specific subclass of [CompletedExceptionally] for cancelled jobs.
 *
 * **Note: This class cannot be used outside of internal coroutines framework**.
 *
 * @param job the job that was cancelled.
 * @param cause the exceptional completion cause. If `cause` is null, then a [JobCancellationException] is created.
 * @suppress **This is unstable API and it is subject to change.**
 */
public class Cancelled(
        private val job: Job,
        cause: Throwable?) : CompletedExceptionally(cause ?: JobCancellationException("Job was cancelled normally", null, job)) {

    override fun isCancelledWithoutCause(): Boolean = cause is JobCancellationException && cause.job == job
}

