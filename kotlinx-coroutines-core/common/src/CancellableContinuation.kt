/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
 * Invocation of [resume] or [resumeWithException] in _resumed_ state produces an [IllegalStateException],
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
     * Same as [tryResume] but with [onCancellation] handler that called if and only if the value is not
     * delivered to the caller because of the dispatch in the process, so that atomicity delivery
     * guaranteed can be provided by having a cancellation fallback.
     */
    @InternalCoroutinesApi
    public fun tryResumeAtomic(value: T, idempotent: Any?, onCancellation: ((cause: Throwable) -> Unit)?): Any?

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
     * @suppress **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun initCancellability()

    /**
     * Cancels this continuation with an optional cancellation `cause`. The result is `true` if this continuation was
     * cancelled as a result of this invocation, and `false` otherwise.
     */
    public fun cancel(cause: Throwable? = null): Boolean

    /**
     * Registers a [handler] to be **synchronously** invoked on [cancellation][cancel] (regular or exceptional) of this continuation.
     * When the continuation is already cancelled, the handler is immediately invoked
     * with the cancellation exception. Otherwise, the handler will be invoked as soon as this
     * continuation is cancelled.
     *
     * The installed [handler] should not throw any exceptions.
     * If it does, they will get caught, wrapped into a [CompletionHandlerException] and
     * processed as an uncaught exception in the context of the current coroutine
     * (see [CoroutineExceptionHandler]).
     *
     * At most one [handler] can be installed on a continuation. Attempt to call `invokeOnCancellation` second
     * time produces [IllegalStateException].
     *
     * This handler is also called when this continuation [resumes][resume] normally (with a value) and then
     * is cancelled while waiting to be dispatched. More generally speaking, this handler is called whenever
     * the caller of [suspendCancellableCoroutine] is getting a [CancellationException].
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
    @ExperimentalCoroutinesApi // since 1.2.0
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
        /*
         * For non-atomic cancellation we setup parent-child relationship immediately
         * in case when `block` blocks the current thread (e.g. Rx2 with trampoline scheduler), but
         * properly supports cancellation.
         */
        cancellable.initCancellability()
        block(cancellable)
        cancellable.getResult()
    }

/**
 * Suspends the coroutine similar to [suspendCancellableCoroutine], but an instance of
 * [CancellableContinuationImpl] is reused.
 */
internal suspend inline fun <T> suspendCancellableCoroutineReusable(
    crossinline block: (CancellableContinuation<T>) -> Unit
): T = suspendCoroutineUninterceptedOrReturn { uCont ->
    val cancellable = getOrCreateCancellableContinuation(uCont.intercepted(), resumeMode = MODE_CANCELLABLE_REUSABLE)
    block(cancellable)
    cancellable.getResult()
}

internal fun <T> getOrCreateCancellableContinuation(
    delegate: Continuation<T>, resumeMode: Int
): CancellableContinuationImpl<T> {
    assert { resumeMode.isReusableMode }
    // If used outside of our dispatcher
    if (delegate !is DispatchedContinuation<T>) {
        return CancellableContinuationImpl(delegate, resumeMode)
    }
    /*
     * Attempt to claim reusable instance.
     *
     * suspendAtomicCancellableCoroutineReusable { // <- claimed
     *     // Any asynchronous cancellation is "postponed" while this block
     *     // is being executed
     * } // postponed cancellation is checked here.
     *
     * Claim can fail for the following reasons:
     * 1) Someone tried to make idempotent resume.
     *    Idempotent resume is internal (used only by us) and is used only in `select`,
     *    thus leaking CC instance for indefinite time.
     * 2) Continuation was cancelled. Then we should prevent any further reuse and bail out.
     */
    return delegate.claimReusableCancellableContinuation()?.takeIf { it.resetState(resumeMode) }
        ?: return CancellableContinuationImpl(delegate, resumeMode)
}

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
public fun CancellableContinuation<*>.disposeOnCancellation(handle: DisposableHandle): Unit =
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
