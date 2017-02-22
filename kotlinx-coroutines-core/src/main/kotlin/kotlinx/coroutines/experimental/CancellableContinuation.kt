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

import kotlinx.coroutines.experimental.internal.LockFreeLinkedListNode
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext
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
 * | ----------------------------------- | ---------- | ------------- | ------------- |
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
    public val isCancelled: Boolean

    /**
     * Tries to resume this continuation with a given value and returns non-null object token if it was successful,
     * or `null` otherwise (it was already resumed or cancelled). When non-null object was returned,
     * [completeResume] must be invoked with it.
     *
     * When [idempotent] is not `null`, this function performs _idempotent_ operation, so that
     * further invocations with the same non-null reference produce the same result.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    public fun tryResume(value: T, idempotent: Any? = null): Any?

    /**
     * Tries to resume this continuation with a given exception and returns non-null object token if it was successful,
     * or `null` otherwise (it was already resumed or cancelled). When non-null object was returned,
     * [completeResume] must be invoked with it.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    public fun tryResumeWithException(exception: Throwable): Any?

    /**
     * Completes the execution of [tryResume] or [tryResumeWithException] on its non-null result.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    public fun completeResume(token: Any)

    /**
     * Makes this continuation cancellable. Use it with `holdCancellability` optional parameter to
     * [suspendCancellableCoroutine] function. It throws [IllegalStateException] if invoked more than once.
     */
    public fun initCancellability()

    /**
     * Resumes this continuation with a given [value] in the invoker thread without going though
     * [dispatch][CoroutineDispatcher.dispatch] function of the [CoroutineDispatcher] in the [context].
     * This function is designed to be used only by the [CoroutineDispatcher] implementations themselves.
     * **It should not be used in general code**.
     *
     * The receiver [CoroutineDispatcher] of this function be equal to the context dispatcher or
     * [IllegalArgumentException] if thrown.
     */
    public fun CoroutineDispatcher.resumeUndispatched(value: T)

    /**
     * Resumes this continuation with a given [exception] in the invoker thread without going though
     * [dispatch][CoroutineDispatcher.dispatch] function of the [CoroutineDispatcher] in the [context].
     * This function is designed to be used only by the [CoroutineDispatcher] implementations themselves.
     * **It should not be used in general code**.
     *
     * The receiver [CoroutineDispatcher] of this function be equal to the context dispatcher or
     * [IllegalArgumentException] if thrown.
     */
    public fun CoroutineDispatcher.resumeUndispatchedWithException(exception: Throwable)
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
        val cancellable = CancellableContinuationImpl(cont, active = true)
        if (!holdCancellability) cancellable.initCancellability()
        block(cancellable)
        cancellable.getResult()
    }


/**
 * Removes a given node on cancellation.
 * @suppress **This is unstable API and it is subject to change.**
 */
public fun CancellableContinuation<*>.removeOnCancel(node: LockFreeLinkedListNode): Job.Registration =
    invokeOnCompletion(RemoveOnCancel(this, node))

// --------------- implementation details ---------------

private class RemoveOnCancel(
    cont: CancellableContinuation<*>,
    val node: LockFreeLinkedListNode
) : JobNode<CancellableContinuation<*>>(cont)  {
    override fun invoke(reason: Throwable?) {
        if (job.isCancelled)
            node.remove()
    }
    override fun toString() = "RemoveOnCancel[$node]"
}

@PublishedApi
internal open class CancellableContinuationImpl<in T>(
    @JvmField
    protected val delegate: Continuation<T>,
    active: Boolean
) : AbstractCoroutine<T>(active), CancellableContinuation<T> {
    @Volatile
    private var decision = UNDECIDED

    override val parentContext: CoroutineContext
        get() = delegate.context

    protected companion object {
        @JvmStatic
        val DECISION: AtomicIntegerFieldUpdater<CancellableContinuationImpl<*>> =
                AtomicIntegerFieldUpdater.newUpdater(CancellableContinuationImpl::class.java, "decision")

        const val UNDECIDED = 0
        const val SUSPENDED = 1
        const val RESUMED = 2

        const val MODE_UNDISPATCHED = 1
        const val MODE_DIRECT = 2

        @Suppress("UNCHECKED_CAST")
        fun <T> getSuccessfulResult(state: Any?): T = if (state is CompletedIdempotentResult) state.result as T else state as T
    }

    override fun initCancellability() {
        initParentJob(delegate.context[Job])
    }

    @PublishedApi
    internal fun getResult(): Any? {
        val decision = this.decision // volatile read
        if (decision == UNDECIDED && DECISION.compareAndSet(this, UNDECIDED, SUSPENDED)) return COROUTINE_SUSPENDED
        // otherwise, afterCompletion was already invoked, and the result is in the state
        val state = this.state
        if (state is CompletedExceptionally) throw state.exception
        return getSuccessfulResult(state)
    }

    override val isCancelled: Boolean get() = state is Cancelled

    override fun tryResume(value: T, idempotent: Any?): Any? {
        while (true) { // lock-free loop on state
            val state = this.state // atomic read
            when (state) {
                is Incomplete -> {
                    val idempotentStart = state.idempotentStart
                    val update: Any? = if (idempotent == null && idempotentStart == null) value else
                        CompletedIdempotentResult(idempotentStart, idempotent, value, state)
                    if (tryUpdateState(state, update)) return state
                }
                is CompletedIdempotentResult -> {
                    if (state.idempotentResume === idempotent) {
                        check(state.result === value) { "Non-idempotent resume" }
                        return state.token
                    } else
                        return null
                }
                else -> return null // cannot resume -- not active anymore
            }
        }
    }

    override fun tryResumeWithException(exception: Throwable): Any? {
        while (true) { // lock-free loop on state
            val state = this.state // atomic read
            when (state) {
                is Incomplete -> {
                    if (tryUpdateState(state, CompletedExceptionally(state.idempotentStart, exception))) return state
                }
                else -> return null // cannot resume -- not active anymore
            }
        }
    }

    override fun completeResume(token: Any) {
        completeUpdateState(token, state, mode = 0)
    }

    override fun afterCompletion(state: Any?, mode: Int) {
        val decision = this.decision // volatile read
        if (decision == UNDECIDED && DECISION.compareAndSet(this, UNDECIDED, RESUMED)) return // will get result in getResult
        // otherwise, getResult has already commenced, i.e. it was resumed later or in other thread
        if (state is CompletedExceptionally) {
            val exception = state.exception
            when (mode) {
                0 -> delegate.resumeWithException(exception)
                MODE_UNDISPATCHED -> (delegate as DispatchedContinuation).resumeUndispatchedWithException(exception)
                MODE_DIRECT -> {
                    if (delegate is DispatchedContinuation)
                        delegate.continuation.resumeWithException(exception)
                    else
                        delegate.resumeWithException(exception)
                }
                else -> error("Invalid mode $mode")
            }
        } else {
            val value = getSuccessfulResult<T>(state)
            when (mode) {
                0 -> delegate.resume(value)
                MODE_UNDISPATCHED -> (delegate as DispatchedContinuation).resumeUndispatched(value)
                MODE_DIRECT -> {
                    if (delegate is DispatchedContinuation)
                        delegate.continuation.resume(value)
                    else
                        delegate.resume(value)
                }
                else -> error("Invalid mode $mode")
            }
        }
    }

    override fun CoroutineDispatcher.resumeUndispatched(value: T) {
        val dc = delegate as? DispatchedContinuation ?: throw IllegalArgumentException("Must be used with DispatchedContinuation")
        check(dc.dispatcher === this) { "Must be invoked from the context CoroutineDispatcher"}
        resume(value, MODE_UNDISPATCHED)
    }

    override fun CoroutineDispatcher.resumeUndispatchedWithException(exception: Throwable) {
        val dc = delegate as? DispatchedContinuation ?: throw IllegalArgumentException("Must be used with DispatchedContinuation")
        check(dc.dispatcher === this) { "Must be invoked from the context CoroutineDispatcher"}
        resumeWithException(exception, MODE_UNDISPATCHED)
    }

    private class CompletedIdempotentResult(
        idempotentStart: Any?,
        @JvmField val idempotentResume: Any?,
        @JvmField val result: Any?,
        @JvmField val token: Incomplete
    ) : CompletedIdempotentStart(idempotentStart) {
        override fun toString(): String = "CompletedIdempotentResult[$result]"
    }
}
