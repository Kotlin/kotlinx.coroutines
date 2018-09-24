/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.intrinsics.*
import kotlinx.coroutines.experimental.selects.*
import kotlin.coroutines.experimental.*

/**
 * Deferred value is a non-blocking cancellable future.
 *
 * It is created with [async][CoroutineScope.async] coroutine builder or via constructor of [CompletableDeferred] class.
 * It is in [active][isActive] state while the value is being computed.
 *
 * Deferred value has the following states:
 *
 * | **State**                               | [isActive] | [isCompleted] | [isCompletedExceptionally] | [isCancelled] |
 * | --------------------------------------- | ---------- | ------------- | -------------------------- | ------------- |
 * | _New_ (optional initial state)          | `false`    | `false`       | `false`                    | `false`       |
 * | _Active_ (default initial state)        | `true`     | `false`       | `false`                    | `false`       |
 * | _Completing_ (optional transient state) | `true`     | `false`       | `false`                    | `false`       |
 * | _Cancelling_ (optional transient state) | `false`    | `false`       | `false`                    | `true`        |
 * | _Cancelled_ (final state)               | `false`    | `true`        | `true`                     | `true`        |
 * | _Resolved_  (final state)               | `false`    | `true`        | `false`                    | `false`       |
 * | _Failed_    (final state)               | `false`    | `true`        | `true`                     | `false`       |
 *
 * Usually, a deferred value is created in _active_ state (it is created and started).
 * However, [async][CoroutineScope.async] coroutine builder has an optional `start` parameter that creates a deferred value in _new_ state
 * when this parameter is set to [CoroutineStart.LAZY].
 * Such a deferred can be be made _active_ by invoking [start], [join], or [await].
 *
 * A deferred can be _cancelled_ at any time with [cancel] function that forces it to transition to
 * _cancelling_ state immediately. Deferred that is not backed by a coroutine (see [CompletableDeferred]) and does not have
 * [children] becomes _cancelled_ on [cancel] immediately.
 * Otherwise, deferred becomes _cancelled_  when it finishes executing its code and
 * when all its children [complete][isCompleted].
 *
 * ```
 *                                                     wait children
 *    +-----+       start      +--------+   complete  +-------------+ finish +-----------+
 *    | New | ---------------> | Active | ----------> | Completing  | ---+-> | Resolved  |
 *    +-----+                  +--------+             +-------------+    |   |(completed)|
 *       |                         |                        |            |   +-----------+
 *       | cancel                  | cancel                 | cancel     |
 *       V                         V                        |            |   +-----------+
 *  +-----------+   finish   +------------+                 |            +-> |  Failed   |
 *  | Cancelled | <--------- | Cancelling | <---------------+                |(completed)|
 *  |(completed)|            +------------+                                  +-----------+
 *  +-----------+
 * ```
 *
 * A deferred value is a [Job]. A job in the
 * [coroutineContext](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.coroutines.experimental/coroutine-context.html)
 * of [async][CoroutineScope.async] builder represents the coroutine itself.
 * A deferred value is active while the coroutine is working and cancellation aborts the coroutine when
 * the coroutine is suspended on a _cancellable_ suspension point by throwing [CancellationException]
 * or the cancellation cause inside the coroutine.
 *
 * A deferred value can have a _parent_ job. A deferred value with a parent is cancelled when its parent is
 * cancelled or completes. Parent waits for all its [children] to complete in _completing_ or
 * _cancelling_ state. _Completing_ state is purely internal. For an outside observer a _completing_
 * deferred is still active, while internally it is waiting for its children.
 *
 * All functions on this interface and on all interfaces derived from it are **thread-safe** and can
 * be safely invoked from concurrent coroutines without external synchronization.
 */
public interface Deferred<out T> : Job {
    /**
     * Returns `true` if computation of this deferred value has _completed exceptionally_ -- it had
     * either _failed_ with exception during computation or was [cancelled][cancel].
     *
     * It implies that [isActive] is `false` and [isCompleted] is `true`.
     */
    public val isCompletedExceptionally: Boolean

    /**
     * Awaits for completion of this value without blocking a thread and resumes when deferred computation is complete,
     * returning the resulting value or throwing the corresponding exception if the deferred had completed exceptionally or was cancelled.
     *
     * This suspending function is cancellable.
     * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
     * immediately resumes with [CancellationException].
     *
     * This function can be used in [select] invocation with [onAwait] clause.
     * Use [isCompleted] to check for completion of this deferred value without waiting.
     */
    public suspend fun await(): T

    /**
     * Clause for [select] expression of [await] suspending function that selects with the deferred value when it is
     * resolved. The [select] invocation fails if the deferred value completes exceptionally (either fails or
     * it cancelled).
     */
    public val onAwait: SelectClause1<T>

    /**
     * Returns *completed* result or throws [IllegalStateException] if this deferred value has not
     * [completed][isCompleted] yet. It throws the corresponding exception if this deferred has
     * [completed exceptionally][isCompletedExceptionally].
     *
     * This function is designed to be used from [invokeOnCompletion] handlers, when there is an absolute certainty that
     * the value is already complete. See also [getCompletionExceptionOrNull].
     *
     * **Note: This is an experimental api.** This function may be removed or renamed in the future.
     */
    @ExperimentalCoroutinesApi
    public fun getCompleted(): T

    /**
     * Returns *completion exception* result if this deferred [completed exceptionally][isCompletedExceptionally],
     * `null` if it is completed normally, or throws [IllegalStateException] if this deferred value has not
     * [completed][isCompleted] yet.
     *
     * This function is designed to be used from [invokeOnCompletion] handlers, when there is an absolute certainty that
     * the value is already complete. See also [getCompleted].
     *
     * **Note: This is an experimental api.** This function may be removed or renamed in the future.
     */
    @ExperimentalCoroutinesApi
    public fun getCompletionExceptionOrNull(): Throwable?

    /**
     * @suppress **Deprecated**: Use `isActive`.
     */
    @Deprecated(message = "Use `isActive`", replaceWith = ReplaceWith("isActive"))
    public val isComputing: Boolean get() = isActive
}

/**
 * @suppress **Deprecated**: onCompletion parameter is deprecated.
 */
@Deprecated("onCompletion parameter is deprecated")
public fun <T> CoroutineScope.async(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): Deferred<T> =
    async(context, start, block).also { if (onCompletion != null) it.invokeOnCompletion(onCompletion) }

/**
 * Creates new coroutine and returns its future result as an implementation of [Deferred].
 * @suppress **Deprecated**. Use [CoroutineScope.async] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.async(context, start, onCompletion, block)", imports = ["kotlinx.coroutines.experimental.*"])
)
public fun <T> async(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): Deferred<T> =
    GlobalScope.async(context, start, onCompletion, block)

/**
 * Creates new coroutine and returns its future result as an implementation of [Deferred].
 * @suppress **Deprecated**. Use [CoroutineScope.async] instead.
 */
@Deprecated(
    message = "Standalone coroutine builders are deprecated, use extensions on CoroutineScope instead",
    replaceWith = ReplaceWith("GlobalScope.async(context + parent, start, onCompletion, block)", imports = ["kotlinx.coroutines.experimental.*"])
)
public fun <T> async(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): Deferred<T> =
    GlobalScope.async(context + (parent ?: EmptyCoroutineContext), start, onCompletion, block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <T> async(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> T
): Deferred<T> =
    GlobalScope.async(context + (parent ?: EmptyCoroutineContext), start, block = block)

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <T> async(
    context: CoroutineContext = Dispatchers.Default,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): Deferred<T> =
    GlobalScope.async(context, start, block = block)

/**
 * @suppress **Deprecated**: Use `start = CoroutineStart.XXX` parameter
 */
@Deprecated(message = "Use `start = CoroutineStart.XXX` parameter",
    replaceWith = ReplaceWith("async(context, if (start) CoroutineStart.DEFAULT else CoroutineStart.LAZY, block)"))
public fun <T> async(context: CoroutineContext, start: Boolean, block: suspend CoroutineScope.() -> T): Deferred<T> =
    GlobalScope.async(context, if (start) CoroutineStart.DEFAULT else CoroutineStart.LAZY, block = block)

/**
 * @suppress **Deprecated**: `defer` was renamed to `async`.
 */
@Deprecated(message = "`defer` was renamed to `async`", level = DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("async(context, block = block)"))
public fun <T> defer(context: CoroutineContext, block: suspend CoroutineScope.() -> T): Deferred<T> =
    GlobalScope.async(context, block = block)

