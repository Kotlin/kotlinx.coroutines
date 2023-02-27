/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
 * An instance of `CancellableContinuation` is created by the [suspendCancellableCoroutine] function.
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
 * invocation of [Continuation.resume] or [Continuation.resumeWithException] transitions it from _active_ to _resumed_ state.
 *
 * A [cancelled][isCancelled] continuation implies that it is [completed][isCompleted].
 *
 * Invocation of [Continuation.resume] or [Continuation.resumeWithException] in _resumed_ state produces an [IllegalStateException],
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
     *
     * Implementation note: current implementation always returns RESUME_TOKEN or `null`
     *
     * @suppress  **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun tryResume(value: T, idempotent: Any?, onCancellation: ((cause: Throwable) -> Unit)?): Any?

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
     * Internal function that setups cancellation behavior in [suspendCancellableCoroutine].
     * It's illegal to call this function in any non-`kotlinx.coroutines` code and
     * such calls lead to undefined behaviour.
     * Exposed in our ABI since 1.0.0 withing `suspendCancellableCoroutine` body.
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
     * This handler is also called when this continuation [resumes][Continuation.resume] normally (with a value) and then
     * is cancelled while waiting to be dispatched. More generally speaking, this handler is called whenever
     * the caller of [suspendCancellableCoroutine] is getting a [CancellationException].
     *
     * A typical example for `invokeOnCancellation` usage is given in
     * the documentation for the [suspendCancellableCoroutine] function.
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
     * code that called the corresponding suspending function, for example:
     *
     * ```
     * continuation.resume(resource) {
     *     resource.close()
     * }
     * ```
     *
     * A more complete example and further details are given in
     * the documentation for the [suspendCancellableCoroutine] function.
     *
     * **Note**: The [onCancellation] handler must be fast, non-blocking, and thread-safe.
     * It can be invoked concurrently with the surrounding code.
     * There is no guarantee on the execution context of its invocation.
     */
    @ExperimentalCoroutinesApi // since 1.2.0
    public fun resume(value: T, onCancellation: ((cause: Throwable) -> Unit)?)
}

/**
 * Suspends the coroutine like [suspendCoroutine], but providing a [CancellableContinuation] to
 * the [block]. This function throws a [CancellationException] if the [Job] of the coroutine is
 * cancelled or completed while it is suspended.
 *
 * A typical use of this function is to suspend a coroutine while waiting for a result
 * from a single-shot callback API and to return the result to the caller.
 * For multi-shot callback APIs see [callbackFlow][kotlinx.coroutines.flow.callbackFlow].
 *
 * ```
 * suspend fun awaitCallback(): T = suspendCancellableCoroutine { continuation ->
 *     val callback = object : Callback { // Implementation of some callback interface
 *         override fun onCompleted(value: T) {
 *             // Resume coroutine with a value provided by the callback
 *             continuation.resume(value)
 *         }
 *         override fun onApiError(cause: Throwable) {
 *             // Resume coroutine with an exception provided by the callback
 *             continuation.resumeWithException(cause)
 *         }
 *     }
 *     // Register callback with an API
 *     api.register(callback)
 *     // Remove callback on cancellation
 *     continuation.invokeOnCancellation { api.unregister(callback) }
 *     // At this point the coroutine is suspended by suspendCancellableCoroutine until callback fires
 * }
 * ```
 *
 * > The callback `register`/`unregister` methods provided by an external API must be thread-safe, because
 * > `invokeOnCancellation` block can be called at any time due to asynchronous nature of cancellation, even
 * > concurrently with the call of the callback.
 *
 * ### Prompt cancellation guarantee
 *
 * This function provides **prompt cancellation guarantee**.
 * If the [Job] of the current coroutine was cancelled while this function was suspended it will not resume
 * successfully.
 *
 * The cancellation of the coroutine's job is generally asynchronous with respect to the suspended coroutine.
 * The suspended coroutine is resumed with the call it to its [Continuation.resumeWith] member function or to
 * [resume][Continuation.resume] extension function.
 * However, when coroutine is resumed, it does not immediately start executing, but is passed to its
 * [CoroutineDispatcher] to schedule its execution when dispatcher's resources become available for execution.
 * The job's cancellation can happen both before, after, and concurrently with the call to `resume`. In any
 * case, prompt cancellation guarantees that the the coroutine will not resume its code successfully.
 *
 * If the coroutine was resumed with an exception (for example, using [Continuation.resumeWithException] extension
 * function) and cancelled, then the resulting exception of the `suspendCancellableCoroutine` function is determined
 * by whichever action (exceptional resume or cancellation) that happened first.
 *
 * ### Returning resources from a suspended coroutine
 *
 * As a result of a prompt cancellation guarantee, when a closeable resource
 * (like open file or a handle to another native resource) is returned from a suspended coroutine as a value
 * it can be lost when the coroutine is cancelled. In order to ensure that the resource can be properly closed
 * in this case, the [CancellableContinuation] interface provides two functions.
 *
 * * [invokeOnCancellation][CancellableContinuation.invokeOnCancellation] installs a handler that is called
 *   whenever a suspend coroutine is being cancelled. In addition to the example at the beginning, it can be
 *   used to ensure that a resource that was opened before the call to
 *   `suspendCancellableCoroutine` or in its body is closed in case of cancellation.
 *
 * ```
 * suspendCancellableCoroutine { continuation ->
 *    val resource = openResource() // Opens some resource
 *    continuation.invokeOnCancellation {
 *        resource.close() // Ensures the resource is closed on cancellation
 *    }
 *    // ...
 * }
 * ```
 *
 * * [resume(value) { ... }][CancellableContinuation.resume] method on a [CancellableContinuation] takes
 *   an optional `onCancellation` block. It can be used when resuming with a resource that must be closed by
 *   the code that called the corresponding suspending function.
 *
 * ```
 * suspendCancellableCoroutine { continuation ->
 *     val callback = object : Callback { // Implementation of some callback interface
 *         // A callback provides a reference to some closeable resource
 *         override fun onCompleted(resource: T) {
 *             // Resume coroutine with a value provided by the callback and ensure the resource is closed in case
 *             // when the coroutine is cancelled before the caller gets a reference to the resource.
 *             continuation.resume(resource) {
 *                 resource.close() // Close the resource on cancellation
 *             }
 *         }
 *     // ...
 * }
 * ```
 *
 * ### Implementation details and custom continuation interceptors
 *
 * The prompt cancellation guarantee is the result of a coordinated implementation inside `suspendCancellableCoroutine`
 * function and the [CoroutineDispatcher] class. The coroutine dispatcher checks for the status of the [Job] immediately
 * before continuing its normal execution and aborts this normal execution, calling all the corresponding
 * cancellation handlers, if the job was cancelled.
 *
 * If a custom implementation of [ContinuationInterceptor] is used in a coroutine's context that does not extend
 * [CoroutineDispatcher] class, then there is no prompt cancellation guarantee. A custom continuation interceptor
 * can resume execution of a previously suspended coroutine even if its job was already cancelled.
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
    crossinline block: (CancellableContinuationImpl<T>) -> Unit
): T = suspendCoroutineUninterceptedOrReturn { uCont ->
    val cancellable = getOrCreateCancellableContinuation(uCont.intercepted())
    block(cancellable)
    cancellable.getResult()
}

internal fun <T> getOrCreateCancellableContinuation(delegate: Continuation<T>): CancellableContinuationImpl<T> {
    // If used outside of our dispatcher
    if (delegate !is DispatchedContinuation<T>) {
        return CancellableContinuationImpl(delegate, MODE_CANCELLABLE)
    }
    /*
     * Attempt to claim reusable instance.
     *
     * suspendCancellableCoroutineReusable { // <- claimed
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
    return delegate.claimReusableCancellableContinuation()?.takeIf { it.resetStateReusable() }
        ?: return CancellableContinuationImpl(delegate, MODE_CANCELLABLE_REUSABLE)
}

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

private class DisposeOnCancel(private val handle: DisposableHandle) : CancelHandler() {
    override fun invoke(cause: Throwable?) = handle.dispose()
    override fun toString(): String = "DisposeOnCancel[$handle]"
}
