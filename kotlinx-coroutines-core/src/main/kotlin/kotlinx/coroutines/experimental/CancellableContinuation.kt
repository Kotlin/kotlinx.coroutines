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

import java.util.concurrent.atomic.AtomicIntegerFieldUpdater
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn
import kotlin.coroutines.experimental.suspendCoroutine

// --------------- cancellable continuations ---------------

/**
 * Cancellable continuation. Its job is _completed_ when it is resumed or cancelled.
 * When [cancel] function is explicitly invoked, this continuation resumes with [CancellationException] or
 * with the specified cancel cause.
 *
 * Cancellable continuation has three states:
 *
 * | **State**                           | [isActive] | [isCompleted] | [isCancelled] |
 * | _Active_ (initial state)            | `true`     | `false`       | `false`       |
 * | _Resumed_ (final _completed_ state) | `false`    | `true`        | `false`       |
 * | _Canceled_ (final _completed_ state)| `false`    | `true`        | `true`        |
 *
 * Invocation of [cancel] transitions this continuation from _active_ to _cancelled_ state, while
 * invocation of [resume] or [resumeWithException] transitions it from _active_ to _resumed_ state.
 *
 * Invocation of [resume] or [resumeWithException] in _resumed_ state produces [IllegalStateException]
 * but is ignored in _cancelled_ state.
 */
public interface CancellableContinuation<in T> : Continuation<T>, Job {
    /**
     * Returns `true` if this continuation was [cancelled][cancel].
     *
     * It implies that [isActive] is `false` and [isCompleted] is `true`.
     */
    val isCancelled: Boolean

    /**
     * Tries to resume this continuation with a given value and returns non-null object token if it was successful,
     * or `null` otherwise (it was already resumed or cancelled). When non-null object was returned,
     * [completeResume] must be invoked with it.
     */
    fun tryResume(value: T): Any?

    /**
     * Tries to resume this continuation with a given exception and returns non-null object token if it was successful,
     * or `null` otherwise (it was already resumed or cancelled). When non-null object was returned,
     * [completeResume] must be invoked with it.
     */
    fun tryResumeWithException(exception: Throwable): Any?

    /**
     * Completes the execution of [tryResume] or [tryResumeWithException] on its non-null result.
     */
    fun completeResume(token: Any)

    /**
     * Makes this continuation cancellable. Use it with `holdCancellability` optional parameter to
     * [suspendCancellableCoroutine] function. It throws [IllegalStateException] if invoked more than once.
     */
    fun initCancellability()
}

/**
 * Suspend coroutine similar to [suspendCoroutine], but provide an implementation of [CancellableContinuation] to
 * the [block]. This function throws [CancellationException] if the coroutine is cancelled while suspended.
 *
 * If [holdCancellability] optional parameter is `true`, then the coroutine is suspended, but it is not
 * cancellable until [CancellableContinuation.initCancellability] is invoked.
 */
public inline suspend fun <T> suspendCancellableCoroutine(
    holdCancellability: Boolean = false,
    crossinline block: (CancellableContinuation<T>) -> Unit
): T =
    suspendCoroutineOrReturn { cont ->
        val safe = SafeCancellableContinuation(cont, getParentJobOrAbort(cont))
        if (!holdCancellability) safe.initCancellability()
        block(safe)
        safe.getResult()
    }

// --------------- implementation details ---------------

@PublishedApi
internal fun getParentJobOrAbort(cont: Continuation<*>): Job? {
    val job = cont.context[Job]
    // fast path when parent job is already complete (we don't even construct SafeCancellableContinuation object)
    if (job != null && !job.isActive) throw job.getCompletionException()
    return job
}

@PublishedApi
internal class SafeCancellableContinuation<in T>(
        private val delegate: Continuation<T>,
        private val parentJob: Job?
) : AbstractCoroutine<T>(delegate.context, active = true), CancellableContinuation<T> {
    // only updated from the thread that invoked suspendCancellableCoroutine

    @Volatile
    private var decision = UNDECIDED

    private companion object {
        val DECISION: AtomicIntegerFieldUpdater<SafeCancellableContinuation<*>> =
                AtomicIntegerFieldUpdater.newUpdater(SafeCancellableContinuation::class.java, "decision")

        const val UNDECIDED = 0
        const val SUSPENDED = 1
        const val RESUMED = 2
        const val YIELD = 3 // used by cancellable "yield"
    }

    override fun initCancellability() {
        initParentJob(parentJob)
    }

    fun getResult(): Any? {
        val decision = this.decision // volatile read
        when (decision) {
            UNDECIDED -> if (DECISION.compareAndSet(this, UNDECIDED, SUSPENDED)) return COROUTINE_SUSPENDED
            YIELD -> return COROUTINE_SUSPENDED
        }
        // otherwise, afterCompletion was already invoked, and the result is in the state
        val state = getState()
        if (state is CompletedExceptionally) throw state.exception
        return state
    }

    override val isCancelled: Boolean
        get() = getState() is Cancelled

    override fun tryResume(value: T): Any? {
        while (true) { // lock-free loop on state
            val state = getState() // atomic read
            when (state) {
                is Incomplete -> if (tryUpdateState(state, value)) return state
                else -> return null // cannot resume -- not active anymore
            }
        }
    }

    override fun tryResumeWithException(exception: Throwable): Any? {
        while (true) { // lock-free loop on state
            val state = getState() // atomic read
            when (state) {
                is Incomplete -> if (tryUpdateState(state, CompletedExceptionally(exception))) return state
                else -> return null // cannot resume -- not active anymore
            }
        }
    }

    override fun completeResume(token: Any) {
        completeUpdateState(token, getState())
    }

    @Suppress("UNCHECKED_CAST")
    override fun afterCompletion(state: Any?) {
        val decision = this.decision // volatile read
        if (decision == UNDECIDED && DECISION.compareAndSet(this, UNDECIDED, RESUMED)) return // will get result in getResult
        // otherwise, getResult has already commenced, i.e. it was resumed later or in other thread
        if (state is CompletedExceptionally)
            delegate.resumeWithException(state.exception)
        else if (decision == YIELD && delegate is DispatchedContinuation)
            delegate.resumeYield(parentJob, state as T)
        else
            delegate.resume(state as T)
    }

    // can only be invoked in the same thread as getResult (see "yield"), afterCompletion may be concurrent
    fun resumeYield(value: T) {
        if ((context[ContinuationInterceptor] as? CoroutineDispatcher)?.isDispatchNeeded(context) == true)
            DECISION.compareAndSet(this, UNDECIDED, YIELD) // try mark as needing dispatch
        resume(value)
    }
}
