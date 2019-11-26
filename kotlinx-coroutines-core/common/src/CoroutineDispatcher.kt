/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * Base class to be extended by all coroutine dispatcher implementations.
 *
 * The following standard implementations are provided by `kotlinx.coroutines` as properties on
 * the [Dispatchers] object:
 *
 * * [Dispatchers.Default] &mdash; is used by all standard builders if no dispatcher or any other [ContinuationInterceptor]
 *   is specified in their context. It uses a common pool of shared background threads.
 *   This is an appropriate choice for compute-intensive coroutines that consume CPU resources.
 * * [Dispatchers.IO] &mdash; uses a shared pool of on-demand created threads and is designed for offloading of IO-intensive _blocking_
 *   operations (like file I/O and blocking socket I/O).
 * * [Dispatchers.Unconfined] &mdash; starts coroutine execution in the current call-frame until the first suspension,
 *   whereupon the coroutine builder function returns.
 *   The coroutine will later resume in whatever thread used by the
 *   corresponding suspending function, without confining it to any specific thread or pool.
 *   **The `Unconfined` dispatcher should not normally be used in code**.
 * * Private thread pools can be created with [newSingleThreadContext] and [newFixedThreadPoolContext].
 * * An arbitrary [Executor][java.util.concurrent.Executor] can be converted to a dispatcher with the [asCoroutineDispatcher] extension function.
 *
 * This class ensures that debugging facilities in [newCoroutineContext] function work properly.
 */
public abstract class CoroutineDispatcher :
    AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {
    /**
     * Returns `true` if the execution shall be dispatched onto another thread.
     * The default behavior for most dispatchers is to return `true`.
     *
     * This method should never be used from general code, it is used only by `kotlinx.coroutines`
     * internals and its contract with the rest of the API is an implementation detail.
     *
     * UI dispatchers _should not_ override `isDispatchNeeded`, but leave the default implementation that
     * returns `true`. To understand the rationale beyond this recommendation, consider the following code:
     *
     * ```kotlin
     * fun asyncUpdateUI() = async(Dispatchers.Main) {
     *     // do something here that updates something in UI
     * }
     * ```
     *
     * When you invoke `asyncUpdateUI` in some background thread, it immediately continues to the next
     * line, while the UI update happens asynchronously in the UI thread. However, if you invoke
     * it in the UI thread itself, it will update the UI _synchronously_ if your `isDispatchNeeded` is
     * overridden with a thread check. Checking if we are already in the UI thread seems more
     * efficient (and it might indeed save a few CPU cycles), but this subtle and context-sensitive
     * difference in behavior makes the resulting async code harder to debug.
     *
     * Basically, the choice here is between the "JS-style" asynchronous approach (async actions
     * are always postponed to be executed later in the event dispatch thread) and "C#-style" approach
     * (async actions are executed in the invoker thread until the first suspension point).
     * While the C# approach seems to be more efficient, it ends up with recommendations like
     * "use `yield` if you need to ....". This is error-prone. The JS-style approach is more consistent
     * and does not require programmers to think about whether they need to yield or not.
     *
     * However, coroutine builders like [launch][CoroutineScope.launch] and [async][CoroutineScope.async] accept an optional [CoroutineStart]
     * parameter that allows one to optionally choose the C#-style [CoroutineStart.UNDISPATCHED] behavior
     * whenever it is needed for efficiency.
     *
     * This method should generally be exception-safe. An exception thrown from this method
     * may leave the coroutines that use this dispatcher in the inconsistent and hard to debug state.
     *
     * **Note: This is an experimental api.** Execution semantics of coroutines may change in the future when this function returns `false`.
     */
    @ExperimentalCoroutinesApi
    public open fun isDispatchNeeded(context: CoroutineContext): Boolean = true

    /**
     * Dispatches execution of a runnable [block] onto another thread in the given [context].
     *
     * This method should generally be exception-safe. An exception thrown from this method
     * may leave the coroutines that use this dispatcher in the inconsistent and hard to debug state.
     *
     * **Note**: This method must not immediately call [block]. Doing so would result in [StackOverflowError]
     * when [yield] is repeatedly called from a loop. However, an implementation that returns `false` from
     * [isDispatchNeeded] can delegate this function to `dispatch` method of [Dispatchers.Unconfined], which is
     * integrated with [yield] to avoid this problem.
     */
    public abstract fun dispatch(context: CoroutineContext, block: Runnable)

    /**
     * Dispatches execution of a runnable `block` onto another thread in the given `context`
     * with a hint for the dispatcher that the current dispatch is triggered by a [yield] call, so that the execution of this
     * continuation may be delayed in favor of already dispatched coroutines.
     *
     * **Implementation note:** Though the `yield` marker may be passed as a part of [context], this
     * is a separate method for performance reasons.
     *
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    public open fun dispatchYield(context: CoroutineContext, block: Runnable) = dispatch(context, block)

    /**
     * Returns a continuation that wraps the provided [continuation], thus intercepting all resumptions.
     *
     * This method should generally be exception-safe. An exception thrown from this method
     * may leave the coroutines that use this dispatcher in the inconsistent and hard to debug state.
     */
    public final override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> =
        DispatchedContinuation(this, continuation)

    @InternalCoroutinesApi
    public override fun releaseInterceptedContinuation(continuation: Continuation<*>) {
        (continuation as DispatchedContinuation<*>).reusableCancellableContinuation?.detachChild()
    }

    /**
     * @suppress **Error**: Operator '+' on two CoroutineDispatcher objects is meaningless.
     * CoroutineDispatcher is a coroutine context element and `+` is a set-sum operator for coroutine contexts.
     * The dispatcher to the right of `+` just replaces the dispatcher to the left.
     */
    @Suppress("DeprecatedCallableAddReplaceWith")
    @Deprecated(
        message = "Operator '+' on two CoroutineDispatcher objects is meaningless. " +
            "CoroutineDispatcher is a coroutine context element and `+` is a set-sum operator for coroutine contexts. " +
            "The dispatcher to the right of `+` just replaces the dispatcher to the left.",
        level = DeprecationLevel.ERROR
    )
    public operator fun plus(other: CoroutineDispatcher) = other

    /** @suppress for nicer debugging */
    override fun toString(): String = "$classSimpleName@$hexAddress"
}

