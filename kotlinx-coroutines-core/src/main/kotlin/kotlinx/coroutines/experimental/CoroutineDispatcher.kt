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

import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Base class that shall be extended by all coroutine dispatcher implementations.
 *
 * The following standard implementations are provided by `kotlinx.coroutines`:
 * * [Unconfined] -- starts coroutine execution in the current call-frame until the first suspension.
 *   On first  suspension the coroutine builder function returns.
 *   The coroutine will resume in whatever thread that is used by the
 *   corresponding suspending function, without confining it to any specific thread or pool.
 *   This in an appropriate choice for IO-intensive coroutines that do not consume CPU resources.
 * * [CommonPool] -- immediately returns from the coroutine builder and schedules coroutine execution to
 *   a common pool of shared background threads.
 *   This is an appropriate choice for compute-intensive coroutines that consume a lot of CPU resources.
 * * Private thread pools can be created with [newSingleThreadContext] and [newFixedThreadPoolContext].
 * * An arbitrary [Executor][java.util.concurrent.Executor] can be converted to dispatcher with [toCoroutineDispatcher] extension function.
 *
 * This class ensures that debugging facilities in [newCoroutineContext] function work properly.
 */
public abstract class CoroutineDispatcher :
        AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {
    /**
     * Return `true` if execution shall be dispatched onto another thread.
     * The default behaviour for most dispatchers is to return `true`.
     */
    public open fun isDispatchNeeded(context: CoroutineContext): Boolean = true

    /**
     * Dispatches execution of a runnable [block] onto another thread in the given [context].
     */
    public abstract fun dispatch(context: CoroutineContext, block: Runnable)

    override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> =
            DispatchedContinuation<T>(this, continuation)

    @Suppress("DeprecatedCallableAddReplaceWith")
    @Deprecated(message = "Operator '+' on two CoroutineDispatcher objects is meaningless. " +
            "CoroutineDispatcher is a coroutine context element and `+` is a set-sum operator for coroutine contexts. " +
            "The dispatcher to the right of `+` just replaces the dispacher the left of `+`.",
            level = DeprecationLevel.ERROR)
    public operator fun plus(other: CoroutineDispatcher) = other
}

internal class DispatchedContinuation<T>(
        val dispatcher: CoroutineDispatcher,
        val continuation: Continuation<T>
): Continuation<T> by continuation {
    override fun resume(value: T) {
        val context = continuation.context
        if (dispatcher.isDispatchNeeded(context))
            dispatcher.dispatch(context, Runnable {
                withCoroutineContext(context) {
                    continuation.resume(value)
                }
            })
        else
            withCoroutineContext(context) {
                continuation.resume(value)
            }
    }

    override fun resumeWithException(exception: Throwable) {
        val context = continuation.context
        if (dispatcher.isDispatchNeeded(context))
            dispatcher.dispatch(context, Runnable {
                withCoroutineContext(context) {
                    continuation.resumeWithException(exception)
                }
            })
        else
            withCoroutineContext(context) {
                continuation.resumeWithException(exception)
            }
    }

    // used by "yield" implementation
    fun resumeYield(job: Job?, value: T) {
        val context = continuation.context
        if (dispatcher.isDispatchNeeded(context))
            dispatcher.dispatch(context, Runnable {
                withCoroutineContext(context) {
                    if (job?.isActive == false)
                        continuation.resumeWithException(job.getCompletionException())
                    else
                        continuation.resume(value)
                }
            })
        else
            withCoroutineContext(context) {
                continuation.resume(value)
            }
    }
}
