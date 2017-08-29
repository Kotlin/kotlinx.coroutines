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

import kotlinx.coroutines.experimental.selects.SelectClause1
import kotlinx.coroutines.experimental.selects.select
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Deferred value is a non-blocking cancellable future.
 *
 * It is created with [async] coroutine builder or via constructor of [CompletableDeferred] class.
 * It is in [active][isActive] state while the value is being computed.
 *
 * Deferred value has the following states:
 *
 * | **State**                               | [isActive] | [isCompleted] | [isCompletedExceptionally] | [isCancelled] |
 * | --------------------------------------- | ---------- | ------------- | -------------------------- | ------------- |
 * | _New_ (optional initial state)          | `false`    | `false`       | `false`                    | `false`       |
 * | _Active_ (default initial state)        | `true`     | `false`       | `false`                    | `false`       |
 * | _Cancelling_ (optional transient state) | `false`    | `false`       | `false`                    | `true`        |
 * | _Cancelled_ (final state)               | `false`    | `true`        | `true`                     | `true`        |
 * | _Resolved_  (final state)               | `false`    | `true`        | `false`                    | `false`       |
 * | _Failed_    (final state)               | `false`    | `true`        | `true`                     | `false`       |
 *
 * Usually, a deferred value is created in _active_ state (it is created and started).
 * However, [async] coroutine builder has an optional `start` parameter that creates a deferred value in _new_ state
 * when this parameter is set to [CoroutineStart.LAZY].
 * Such a deferred can be be made _active_ by invoking [start], [join], or [await].
 *
 * A deferred can be _cancelled_ at any time with [cancel] function that forces it to transition to
 * _cancelling_ state immediately. A simple implementation of deferred -- [CompletableDeferred],
 * that is not backed by a coroutine, does not have a _cancelling_ state, but becomes _cancelled_
 * on [cancel] immediately. Coroutines, on the other hand, become _cancelled_ only when they finish
 * executing their code.
 *
 * ```
 *    +-----+       start      +--------+   complete   +-----------+
 *    | New | ---------------> | Active | ---------+-> | Resolved  |
 *    +-----+                  +--------+          |   |(completed)|
 *       |                         |               |   +-----------+
 *       | cancel                  | cancel        |
 *       V                         V               |   +-----------+
 *  +-----------+   finish   +------------+        +-> |  Failed   |
 *  | Cancelled | <--------- | Cancelling |            |(completed)|
 *  |(completed)|            +------------+            +-----------+
 *  +-----------+
 * ```
 *
 * A deferred value is a [Job]. A job in the coroutine [context][CoroutineScope.context] of [async] builder
 * represents the coroutine itself.
 * A deferred value is active while the coroutine is working and cancellation aborts the coroutine when
 * the coroutine is suspended on a _cancellable_ suspension point by throwing [CancellationException]
 * or the cancellation cause inside the coroutine.
 *
 * A deferred value can have a _parent_ job. A deferred value with a parent is cancelled when its parent is
 * cancelled or completes.
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
    val isCompletedExceptionally: Boolean

    /**
     * Awaits for completion of this value without blocking a thread and resumes when deferred computation is complete,
     * returning the resulting value or throwing the corresponding exception if the deferred had completed exceptionally.
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
     * the value is already complete.
     */
    public fun getCompleted(): T

    /**
     * @suppress **Deprecated**: Use `isActive`.
     */
    @Deprecated(message = "Use `isActive`", replaceWith = ReplaceWith("isActive"))
    public val isComputing: Boolean get() = isActive
}

/**
 * Creates new coroutine and returns its future result as an implementation of [Deferred].
 *
 * The running coroutine is cancelled when the resulting object is [cancelled][Job.cancel].
 * The [context] for the new coroutine must be explicitly specified.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * An optional [start] parameter can be set to [CoroutineStart.LAZY] to start coroutine _lazily_. In this case,,
 * the resulting [Deferred] is created in _new_ state. It can be explicitly started with [start][Job.start]
 * function and will be started implicitly on the first invocation of [join][Job.join] or [await][Deferred.await].
 *
 * @param context context of the coroutine
 * @param start coroutine start option
 * @param block the coroutine code
 */
public fun <T> async(
    context: CoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): Deferred<T> {
    val newContext = newCoroutineContext(context)
    val coroutine = if (start.isLazy)
        LazyDeferredCoroutine(newContext, block) else
        DeferredCoroutine<T>(newContext, active = true)
    coroutine.initParentJob(context[Job])
    start(block, coroutine, coroutine)
    return coroutine
}

/**
 * @suppress **Deprecated**: Use `start = CoroutineStart.XXX` parameter
 */
@Deprecated(message = "Use `start = CoroutineStart.XXX` parameter",
    replaceWith = ReplaceWith("async(context, if (start) CoroutineStart.DEFAULT else CoroutineStart.LAZY, block)"))
public fun <T> async(context: CoroutineContext, start: Boolean, block: suspend CoroutineScope.() -> T): Deferred<T> =
    async(context, if (start) CoroutineStart.DEFAULT else CoroutineStart.LAZY, block)

/**
 * @suppress **Deprecated**: `defer` was renamed to `async`.
 */
@Deprecated(message = "`defer` was renamed to `async`", level = DeprecationLevel.WARNING,
        replaceWith = ReplaceWith("async(context, block = block)"))
public fun <T> defer(context: CoroutineContext, block: suspend CoroutineScope.() -> T): Deferred<T> =
    async(context, block = block)

@Suppress("UNCHECKED_CAST")
private open class DeferredCoroutine<T>(
    parentContext: CoroutineContext,
    active: Boolean
) : AbstractCoroutine<T>(parentContext, active), Deferred<T> {
    override fun getCompleted(): T = getCompletedInternal() as T
    suspend override fun await(): T = awaitInternal() as T
    override val onAwait: SelectClause1<T>
        get() = this as SelectClause1<T>
}

private class LazyDeferredCoroutine<T>(
    parentContext: CoroutineContext,
    private val block: suspend CoroutineScope.() -> T
) : DeferredCoroutine<T>(parentContext, active = false) {
    override fun onStart() {
        block.startCoroutineCancellable(this, this)
    }
}
