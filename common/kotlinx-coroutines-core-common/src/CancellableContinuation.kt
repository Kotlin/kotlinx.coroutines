/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

// --------------- cancellable continuations ---------------

/**
 * Cancellable continuation. It is _completed_ when it is resumed or cancelled.
 * When [cancel] function is explicitly invoked, this continuation immediately resumes with [CancellationException] or
 * with the specified cancel cause.
 *
 * Cancellable continuation has three states (as subset of [Job] states):
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
 * A [cancelled][isCancelled] continuation implies that it is [completed][isCompleted].
 *
 * Invocation of [resume] or [resumeWithException] in _resumed_ state produces [IllegalStateException]
 * but is ignored in _cancelled_ state.
 *
 * ```
 *    +-----------+   resume    +---------+
 *    |  Active   | ----------> | Resumed |
 *    +-----------+             +---------+
 *          |
 *          | cancel
 *          V
 *    +-----------+
 *    | Cancelled |
 *    +-----------+
 *
 * ```
 */
public interface CancellableContinuation<in T> : Continuation<T> {
    /**
     * Returns `true` when this continuation is active -- it has not completed or cancelled yet.
     */
    public val isActive: Boolean

    /**
     * Returns `true` when this continuation has completed for any reason. A continuation
     * that was cancelled is also considered complete.
     */
    public val isCompleted: Boolean

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
    @InternalCoroutinesApi
    public fun tryResume(value: T, idempotent: Any? = null): Any?

    /**
     * Tries to resume this continuation with a given exception and returns non-null object token if it was successful,
     * or `null` otherwise (it was already resumed or cancelled). When non-null object was returned,
     * [completeResume] must be invoked with it.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun tryResumeWithException(exception: Throwable): Any?

    /**
     * Completes the execution of [tryResume] or [tryResumeWithException] on its non-null result.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun completeResume(token: Any)

    /**
     * Makes this continuation cancellable. Use it with `holdCancellability` optional parameter to
     * [suspendCancellableCoroutine] function. It throws [IllegalStateException] if invoked more than once.
     */
    @InternalCoroutinesApi
    public fun initCancellability()

    /**
     * Cancels this continuation with an optional cancellation [cause]. The result is `true` if this continuation was
     * cancelled as a result of this invocation and `false` otherwise.
     */
    public fun cancel(cause: Throwable? = null): Boolean

    /**
     * Registers handler that is **synchronously** invoked once on cancellation (both regular and exceptional) of this continuation.
     * When the continuation is already cancelled, then the handler is immediately invoked
     * with cancellation exception. Otherwise, the handler will be invoked once on cancellation if this
     * continuation is cancelled.
     *
     * Installed [handler] should not throw any exceptions. If it does, they will get caught,
     * wrapped into [CompletionHandlerException], and rethrown, potentially causing the crash of unrelated code.
     *
     * At most one [handler] can be installed on one continuation
     *
     * @param invokeImmediately not used
     * @param onCancelling not used
     * @return not used
     */
    @Deprecated(
        message = "Disposable handlers on regular completion are no longer supported",
        replaceWith = ReplaceWith("invokeOnCancellation(handler)"),
        level = DeprecationLevel.WARNING
    )
    public fun invokeOnCompletion(
        onCancelling: Boolean = false,
        invokeImmediately: Boolean = true,
        handler: CompletionHandler): DisposableHandle

    /**
     * Registers handler that is **synchronously** invoked once on cancellation (both regular and exceptional) of this continuation.
     * When the continuation is already cancelled, then the handler is immediately invoked
     * with cancellation exception. Otherwise, the handler will be invoked once on cancellation if this
     * continuation is cancelled.
     *
     * Installed [handler] should not throw any exceptions. If it does, they will get caught,
     * wrapped into [CompletionHandlerException], and rethrown, potentially causing the crash of unrelated code.
     *
     * At most one [handler] can be installed on one continuation.
     */
    public fun invokeOnCancellation(handler: CompletionHandler)

    /**
     * Resumes this continuation with a given [value] in the invoker thread without going though
     * [dispatch][CoroutineDispatcher.dispatch] function of the [CoroutineDispatcher] in the [context].
     * This function is designed to be used only by the [CoroutineDispatcher] implementations themselves.
     * **It should not be used in general code**.
     *
     * **Note: This function is experimental.** Its signature general code may be changed in the future.
     */
    @ExperimentalCoroutinesApi
    public fun CoroutineDispatcher.resumeUndispatched(value: T)

    /**
     * Resumes this continuation with a given [exception] in the invoker thread without going though
     * [dispatch][CoroutineDispatcher.dispatch] function of the [CoroutineDispatcher] in the [context].
     * This function is designed to be used only by the [CoroutineDispatcher] implementations themselves.
     * **It should not be used in general code**.
     *
     * **Note: This function is experimental.** Its signature general code may be changed in the future.
     */
    @ExperimentalCoroutinesApi
    public fun CoroutineDispatcher.resumeUndispatchedWithException(exception: Throwable)
}

/**
 * Suspends coroutine similar to [suspendCoroutine], but provide an implementation of [CancellableContinuation] to
 * the [block]. This function throws [CancellationException] if the coroutine is cancelled or completed while suspended.
 */
public suspend inline fun <T> suspendCancellableCoroutine(
    crossinline block: (CancellableContinuation<T>) -> Unit
): T =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val cancellable = CancellableContinuationImpl(uCont.intercepted(), resumeMode = MODE_CANCELLABLE)
        cancellable.initCancellability()
        block(cancellable)
        cancellable.getResult()
    }

@Suppress("DeprecatedCallableAddReplaceWith")
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "holdCancellability is no longer supported, no replacement"
)
public suspend inline fun <T> suspendCancellableCoroutine(
    holdCancellability: Boolean = false,
    crossinline block: (CancellableContinuation<T>) -> Unit
): T = error("holdCancellability is no longer supported, no replacement")

/**
 * Suspends coroutine similar to [suspendCancellableCoroutine], but with *atomic cancellation*.
 *
 * When suspended function throws [CancellationException] it means that the continuation was not resumed.
 * As a side-effect of atomic cancellation, a thread-bound coroutine (to some UI thread, for example) may
 * continue to execute even after it was cancelled from the same thread in the case when the continuation
 * was already resumed and was posted for execution to the thread's queue.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public suspend inline fun <T> suspendAtomicCancellableCoroutine(
    holdCancellability: Boolean = false,
    crossinline block: (CancellableContinuation<T>) -> Unit
): T =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val cancellable = CancellableContinuationImpl(uCont.intercepted(), resumeMode = MODE_ATOMIC_DEFAULT)
        if (!holdCancellability) cancellable.initCancellability()
        block(cancellable)
        cancellable.getResult()
    }

/**
 * Removes a given node on cancellation.
 * @suppress **This is unstable API and it is subject to change.**
 */
@Deprecated(
    message = "Disposable handlers on cancellation are no longer supported",
    replaceWith = ReplaceWith("removeOnCancellation(handler)"),
    level = DeprecationLevel.WARNING)
public fun CancellableContinuation<*>.removeOnCancel(node: LockFreeLinkedListNode): DisposableHandle {
    removeOnCancellation(node)
    return NonDisposableHandle
}

/**
 * Removes a given node on cancellation.
 * @suppress **This is unstable API and it is subject to change.**
 */
public fun CancellableContinuation<*>.removeOnCancellation(node: LockFreeLinkedListNode) =
    invokeOnCancellation(handler = RemoveOnCancel(node).asHandler)

/**
 * Disposes a specified [handle] when this continuation is cancelled.
 *
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCancellation { handle.dispose() }
 * ```
 */
@Deprecated(
    message = "Disposable handlers on regular completion are no longer supported",
    replaceWith = ReplaceWith("disposeOnCancellation(handler)"),
    level = DeprecationLevel.WARNING)
public fun CancellableContinuation<*>.disposeOnCompletion(handle: DisposableHandle): DisposableHandle {
    disposeOnCancellation(handle)
    return NonDisposableHandle
}

/**
 * Disposes a specified [handle] when this continuation is cancelled.
 *
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCancellation { handle.dispose() }
 * ```
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public fun CancellableContinuation<*>.disposeOnCancellation(handle: DisposableHandle) =
    invokeOnCancellation(handler = DisposeOnCancel(handle).asHandler)

// --------------- implementation details ---------------

private class RemoveOnCancel(private val node: LockFreeLinkedListNode) : CancelHandler() {
    override fun invoke(cause: Throwable?) { node.remove() }
    override fun toString() = "RemoveOnCancel[$node]"
}

private class DisposeOnCancel(private val handle: DisposableHandle) : CancelHandler() {
    override fun invoke(cause: Throwable?) = handle.dispose()
    override fun toString(): String = "DisposeOnCancel[$handle]"
}

@PublishedApi
internal open class CancellableContinuationImpl<in T>(
    delegate: Continuation<T>,
    resumeMode: Int
) : AbstractContinuation<T>(delegate, resumeMode), CancellableContinuation<T>, Runnable {

    public override val context: CoroutineContext = delegate.context

    override fun initCancellability() {
        initParentJobInternal(delegate.context[Job])
    }

    override fun invokeOnCompletion(onCancelling: Boolean,
        invokeImmediately: Boolean, handler: CompletionHandler): DisposableHandle {
        invokeOnCancellation(handler)
        return NonDisposableHandle
    }

    override fun tryResume(value: T, idempotent: Any?): Any? {
        loopOnState { state ->
            when (state) {
                is NotCompleted -> {
                    val update: Any? = if (idempotent == null) value else
                        CompletedIdempotentResult(idempotent, value, state)
                    if (tryUpdateStateToFinal(state, update)) return state
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
        loopOnState { state ->
            when (state) {
                is NotCompleted -> {
                    if (tryUpdateStateToFinal(state, CompletedExceptionally(exception))) return state
                }
                else -> return null // cannot resume -- not active anymore
            }
        }
    }

    override fun completeResume(token: Any) = completeStateUpdate(token as NotCompleted, state, resumeMode)

    override fun CoroutineDispatcher.resumeUndispatched(value: T) {
        val dc = delegate as? DispatchedContinuation
        resumeImpl(value, if (dc?.dispatcher === this) MODE_UNDISPATCHED else resumeMode)
    }

    override fun CoroutineDispatcher.resumeUndispatchedWithException(exception: Throwable) {
        val dc = delegate as? DispatchedContinuation
        resumeImpl(CompletedExceptionally(exception), if (dc?.dispatcher === this) MODE_UNDISPATCHED else resumeMode)
    }

    @Suppress("UNCHECKED_CAST")
    override fun <T> getSuccessfulResult(state: Any?): T =
        if (state is CompletedIdempotentResult) state.result as T else state as T

    protected override fun nameString(): String =
        "CancellableContinuation(${delegate.toDebugString()})"
}

private class CompletedIdempotentResult(
    @JvmField val idempotentResume: Any?,
    @JvmField val result: Any?,
    @JvmField val token: NotCompleted
) {
    override fun toString(): String = "CompletedIdempotentResult[$result]"
}
