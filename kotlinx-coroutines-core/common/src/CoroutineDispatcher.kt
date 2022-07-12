/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
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

    /** @suppress */
    @ExperimentalStdlibApi
    public companion object Key : AbstractCoroutineContextKey<ContinuationInterceptor, CoroutineDispatcher>(
        ContinuationInterceptor,
        { it as? CoroutineDispatcher })

    /**
     * Returns `true` if the execution of the coroutine should be performed with [dispatch] method.
     * The default behavior for most dispatchers is to return `true`.
     *
     * If this method returns `false`, the coroutine is resumed immediately in the current thread,
     * potentially forming an event-loop to prevent stack overflows.
     * The event loop is an advanced topic and its implications can be found in [Dispatchers.Unconfined] documentation.
     *
     * The [context] parameter represents the context of the coroutine that is being dispatched,
     * or [EmptyCoroutineContext] if a non-coroutine-specific [Runnable] is dispatched instead.
     *
     * A dispatcher can override this method to provide a performance optimization and avoid paying a cost of an unnecessary dispatch.
     * E.g. [MainCoroutineDispatcher.immediate] checks whether we are already in the required UI thread in this method and avoids
     * an additional dispatch when it is not required.
     *
     * While this approach can be more efficient, it is not chosen by default to provide a consistent dispatching behaviour
     * so that users won't observe unexpected and non-consistent order of events by default.
     *
     * Coroutine builders like [launch][CoroutineScope.launch] and [async][CoroutineScope.async] accept an optional [CoroutineStart]
     * parameter that allows one to optionally choose the [undispatched][CoroutineStart.UNDISPATCHED] behavior to start coroutine immediately,
     * but to be resumed only in the provided dispatcher.
     *
     * This method should generally be exception-safe. An exception thrown from this method
     * may leave the coroutines that use this dispatcher in the inconsistent and hard to debug state.
     *
     * @see dispatch
     * @see Dispatchers.Unconfined
     */
    public open fun isDispatchNeeded(context: CoroutineContext): Boolean = true

    /**
     * Creates a view of the current dispatcher that limits the parallelism to the given [value][parallelism].
     * The resulting view uses the original dispatcher for execution, but with the guarantee that
     * no more than [parallelism] coroutines are executed at the same time.
     *
     * This method does not impose restrictions on the number of views or the total sum of parallelism values,
     * each view controls its own parallelism independently with the guarantee that the effective parallelism
     * of all views cannot exceed the actual parallelism of the original dispatcher.
     *
     * ### Limitations
     *
     * The default implementation of `limitedParallelism` does not support direct dispatchers,
     * such as executing the given runnable in place during [dispatch] calls.
     * Any dispatcher that may return `false` from [isDispatchNeeded] is considered direct.
     * For direct dispatchers, it is recommended to override this method
     * and provide a domain-specific implementation or to throw an [UnsupportedOperationException].
     *
     * ### Example of usage
     * ```
     * private val backgroundDispatcher = newFixedThreadPoolContext(4, "App Background")
     * // At most 2 threads will be processing images as it is really slow and CPU-intensive
     * private val imageProcessingDispatcher = backgroundDispatcher.limitedParallelism(2)
     * // At most 3 threads will be processing JSON to avoid image processing starvation
     * private val jsonProcessingDispatcher = backgroundDispatcher.limitedParallelism(3)
     * // At most 1 thread will be doing IO
     * private val fileWriterDispatcher = backgroundDispatcher.limitedParallelism(1)
     * ```
     * Note how in this example the application has an executor with 4 threads, but the total sum of all limits
     * is 6. Still, at most 4 coroutines can be executed simultaneously as each view limits only its own parallelism.
     *
     * Note that this example was structured in such a way that it illustrates the parallelism guarantees.
     * In practice, it is usually better to use [Dispatchers.IO] or [Dispatchers.Default] instead of creating a
     * `backgroundDispatcher`. It is both possible and advised to call `limitedParallelism` on them.
     */
    @ExperimentalCoroutinesApi
    public open fun limitedParallelism(parallelism: Int): CoroutineDispatcher {
        parallelism.checkParallelism()
        return LimitedDispatcher(this, parallelism)
    }

    /**
     * Requests execution of a runnable [block].
     * The dispatcher guarantees that [block] will eventually execute, typically by dispatching it to a thread pool,
     * using a dedicated thread, or just executing the block in place.
     * The [context] parameter represents the context of the coroutine that is being dispatched,
     * or [EmptyCoroutineContext] if a non-coroutine-specific [Runnable] is dispatched instead.
     * Implementations may use [context] for additional context-specific information,
     * such as priority, whether the dispatched coroutine can be invoked in place,
     * coroutine name, and additional diagnostic elements.
     *
     * This method should guarantee that the given [block] will be eventually invoked,
     * otherwise the system may reach a deadlock state and never leave it.
     * The cancellation mechanism is transparent for [CoroutineDispatcher] and is managed by [block] internals.
     *
     * This method should generally be exception-safe. An exception thrown from this method
     * may leave the coroutines that use this dispatcher in an inconsistent and hard-to-debug state.
     *
     * This method must not immediately call [block]. Doing so may result in `StackOverflowError`
     * when `dispatch` is invoked repeatedly, for example when [yield] is called in a loop.
     * In order to execute a block in place, it is required to return `false` from [isDispatchNeeded]
     * and delegate the `dispatch` implementation to `Dispatchers.Unconfined.dispatch` in such cases.
     * To support this, the coroutines machinery ensures in-place execution and forms an event-loop to
     * avoid unbound recursion.
     *
     * @see isDispatchNeeded
     * @see Dispatchers.Unconfined
     */
    public abstract fun dispatch(context: CoroutineContext, block: Runnable)

    /**
     * Dispatches execution of a runnable `block` onto another thread in the given `context`
     * with a hint for the dispatcher that the current dispatch is triggered by a [yield] call, so that the execution of this
     * continuation may be delayed in favor of already dispatched coroutines.
     *
     * Though the `yield` marker may be passed as a part of [context], this
     * is a separate method for performance reasons.
     *
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    public open fun dispatchYield(context: CoroutineContext, block: Runnable): Unit = dispatch(context, block)

    /**
     * Returns a continuation that wraps the provided [continuation], thus intercepting all resumptions.
     *
     * This method should generally be exception-safe. An exception thrown from this method
     * may leave the coroutines that use this dispatcher in the inconsistent and hard to debug state.
     */
    public final override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> =
        DispatchedContinuation(this, continuation)

    public final override fun releaseInterceptedContinuation(continuation: Continuation<*>) {
        /*
         * Unconditional cast is safe here: we only return DispatchedContinuation from `interceptContinuation`,
         * any ClassCastException can only indicate compiler bug
         */
        val dispatched = continuation as DispatchedContinuation<*>
        dispatched.release()
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
    public operator fun plus(other: CoroutineDispatcher): CoroutineDispatcher = other

    /** @suppress for nicer debugging */
    override fun toString(): String = "$classSimpleName@$hexAddress"
}

