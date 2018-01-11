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

/**
 * Class for an internal state of a job that had completed exceptionally, including cancellation.
 *
 * **Note: This class cannot be used outside of internal coroutines framework**.
 *
 * @param cause the exceptional completion cause. If `cause` is null, then an exception is
 *        if created via [createException] on first get from [exception] property.
 * @param allowNullCause if `null` cause is allowed.
 * @suppress **This is unstable API and it is subject to change.**
 */
public open class CompletedExceptionally protected constructor(
    public val cause: Throwable?,
    allowNullCause: Boolean
) {
    /**
     * Creates exceptionally completed state.
     * @param cause the exceptional completion cause.
     */
    public constructor(cause: Throwable) : this(cause, false)

    @Volatile
    private var _exception: Throwable? = cause // will materialize JobCancellationException on first need

    init {
        require(allowNullCause || cause != null) { "Null cause is not allowed" }
    }

    /**
     * Returns completion exception.
     */
    public val exception: Throwable get() =
        _exception ?: // atomic read volatile var or else create new
            createException().also { _exception = it }

    protected open fun createException(): Throwable = error("Completion exception was not specified")

    override fun toString(): String = "${this::class.simpleName}[$exception]"
}

/**
 * A specific subclass of [CompletedExceptionally] for cancelled jobs.
 *
 * **Note: This class cannot be used outside of internal coroutines framework**.
 * 
 * @param job the job that was cancelled.
 * @param cause the exceptional completion cause. If `cause` is null, then a [JobCancellationException]
 *        if created on first get from [exception] property.
 * @suppress **This is unstable API and it is subject to change.**
 */
public class Cancelled(
    private val job: Job,
    cause: Throwable?
) : CompletedExceptionally(cause, true) {
    override fun createException(): Throwable = JobCancellationException("Job was cancelled normally", null, job)
}

