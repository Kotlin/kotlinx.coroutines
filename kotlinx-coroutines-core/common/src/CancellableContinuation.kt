/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

// --------------- cancellable continuations ---------------

/**
 * Cancellable continuation. It is _completed_ when resumed or cancelled.
 * When the [cancel] function is explicitly invoked, this continuation immediately resumes with a [CancellationException] or
 * the specified cancel cause.
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
 * Invocation of [resume] or [resumeWithException] in _resumed_ state produces an [IllegalStateException].
 * Invocation of [resume] in _cancelled_ state is ignored (it is a trivial race between resume from the continuation owner and
 * outer job's cancellation, and the cancellation wins).
 * Invocation of [resumeWithException] in _cancelled_ state triggers exception handling of the passed exception.
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
     * Returns `true` when this continuation has completed for any reason. A cancelled continuation
     * is also considered complete.
     */
    public val isCompleted: Boolean

    /**
     * Returns `true` if this continuation was [cancelled][cancel].
     *
     * It implies that [isActive] is `false` and [isCompleted] is `true`.
     */
    public val isCancelled: Boolean

    /**
     * Tries to resume this continuation with the specified [value] and returns a non-null object token if successful,
     * or `null` otherwise (it was already resumed or cancelled). When a non-null object is returned,
     * [completeResume] must be invoked with it.
     *
     * When [idempotent] is not `null`, this function performs an _idempotent_ operation, so that
     * further invocations with the same non-null reference produce the same result.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun tryResume(value: T, idempotent: Any? = null): Any?

    /**
     * Tries to resume this continuation with the specified [exception] and returns a non-null object token if successful,
     * or `null` otherwise (it was already resumed or cancelled). When a non-null object is returned,
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
     * Legacy function that turned on cancellation behavior in [suspendCancellableCoroutine] before kotlinx.coroutines 1.1.0.
     * This function does nothing and is left only for binary compatibility with old compiled code.
     *
     * @suppress **Deprecated**: This function is no longer used.
     *   It is left for binary compatibility with code compiled before kotlinx.coroutines 1.1.0.
     */
    @Deprecated(
        level = DeprecationLevel.HIDDEN,
        message = "This function is no longer used. " +
            "It is left for binary compatibility with code compiled before kotlinx.coroutines 1.1.0. "
    )
    @InternalCoroutinesApi
    public fun initCancellability()

    /**
     * Cancels this continuation with an optional cancellation `cause`. The result is `true` if this continuation was
     * cancelled as a result of this invocation, and `false` otherwise.
     */
    public fun cancel(cause: Throwable? = null): Boolean

    /**
     * Registers a [handler] to be **synchronously** invoked on cancellation (regular or exceptional) of this continuation.
     * When the continuation is already cancelled, the handler will be immediately invoked
     * with the cancellation exception. Otherwise, the handler will be invoked as soon as this
     * continuation is cancelled.
     *
     * The installed [handler] should not throw any exceptions.
     * If it does, they will get caught, wrapped into a [CompletionHandlerException] and
     * processed as an uncaught exception in the context of the current coroutine
     * (see [CoroutineExceptionHandler]).
     *
     * At most one [handler] can be installed on a continuation.
     *
     * **Note**: Implementation of `CompletionHandler` must be fast, non-blocking, and thread-safe.
     * This `handler` can be invoked concurrently with the surrounding code.
     * There is no guarantee on the execution context in which the `handler` will be invoked.
     */
    public fun invokeOnCancellation(handler: CompletionHandler)

    /**
     * Resumes this continuation with the specified [value] in the invoker thread without going through
     * the [dispatch][CoroutineDispatcher.dispatch] function of the [CoroutineDispatcher] in the [context].
     * This function is designed to only be used by [CoroutineDispatcher] implementations.
     * **It should not be used in general code**.
     *
     * **Note: This function is experimental.** Its signature general code may be changed in the future.
     */
    @ExperimentalCoroutinesApi
    public fun CoroutineDispatcher.resumeUndispatched(value: T)

    /**
     * Resumes this continuation with the specified [exception] in the invoker thread without going through
     * the [dispatch][CoroutineDispatcher.dispatch] function of the [CoroutineDispatcher] in the [context].
     * This function is designed to only be used by [CoroutineDispatcher] implementations.
     * **It should not be used in general code**.
     *
     * **Note: This function is experimental.** Its signature general code may be changed in the future.
     */
    @ExperimentalCoroutinesApi
    public fun CoroutineDispatcher.resumeUndispatchedWithException(exception: Throwable)

    /**
     * Resumes this continuation with the specified `value` and calls the specified `onCancellation`
     * handler when either resumed too late (when continuation was already cancelled) or, although resumed
     * successfully (before cancellation), the coroutine's job was cancelled before it had a
     * chance to run in its dispatcher, so that the suspended function threw an exception
     * instead of returning this value.
     *
     * The installed [onCancellation] handler should not throw any exceptions.
     * If it does, they will get caught, wrapped into a [CompletionHandlerException] and
     * processed as an uncaught exception in the context of the current coroutine
     * (see [CoroutineExceptionHandler]).
     *
     * This function shall be used when resuming with a resource that must be closed by
     * code that called the corresponding suspending function, e.g.:
     *
     * ```
     * continuation.resume(resource) {
     *     resource.close()
     * }
     * ```
     *
     * **Note**: The [onCancellation] handler must be fast, non-blocking, and thread-safe.
     * It can be invoked concurrently with the surrounding code.
     * There is no guarantee on the execution context of its invocation.
     */
    @ExperimentalCoroutinesApi // since 1.2.0, tentatively graduates in 1.3.0
    public fun resume(value: T, onCancellation: (cause: Throwable) -> Unit)
}

/**
 * Suspends the coroutine like [suspendCoroutine], but providing a [CancellableContinuation] to
 * the [block]. This function throws a [CancellationException] if the coroutine is cancelled or completed while suspended.
 */
public suspend inline fun <T> suspendCancellableCoroutine(
    crossinline block: (CancellableContinuation<T>) -> Unit
): T =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val cancellable = CancellableContinuationImpl(uCont.intercepted(), resumeMode = MODE_CANCELLABLE)
        // NOTE: Before version 1.1.0 the following invocation was inlined here, so invocation of this
        // method indicates that the code was compiled by kotlinx.coroutines < 1.1.0
        // cancellable.initCancellability()
        block(cancellable)
        cancellable.getResult()
    }

/**
 * Suspends the coroutine like [suspendCancellableCoroutine], but with *atomic cancellation*.
 *
 * When the suspended function throws a [CancellationException], it means that the continuation was not resumed.
 * As a side-effect of atomic cancellation, a thread-bound coroutine (to some UI thread, for example) may
 * continue to execute even after it was cancelled from the same thread in the case when the continuation
 * was already resumed and was posted for execution to the thread's queue.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public suspend inline fun <T> suspendAtomicCancellableCoroutine(
    crossinline block: (CancellableContinuation<T>) -> Unit
): T =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val cancellable = CancellableContinuationImpl(uCont.intercepted(), resumeMode = MODE_ATOMIC_DEFAULT)
        block(cancellable)
        cancellable.getResult()
    }

/**
 * @suppress **Deprecated**
 */
@Deprecated(
    message = "holdCancellability parameter is deprecated and is no longer used",
    replaceWith = ReplaceWith("suspendAtomicCancellableCoroutine(block)")
)
@InternalCoroutinesApi
public suspend inline fun <T> suspendAtomicCancellableCoroutine(
    holdCancellability: Boolean = false,
    crossinline block: (CancellableContinuation<T>) -> Unit
): T =
    suspendAtomicCancellableCoroutine(block)

/**
 * Removes the specified [node] on cancellation.
 */
internal fun CancellableContinuation<*>.removeOnCancellation(node: LockFreeLinkedListNode) =
    invokeOnCancellation(handler = RemoveOnCancel(node).asHandler)

/**
 * Disposes the specified [handle] when this continuation is cancelled.
 *
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created):
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
