/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.intrinsics.*
import kotlinx.coroutines.experimental.selects.*
import kotlin.coroutines.experimental.*

/**
 * Deferred value is a non-blocking cancellable future &mdash; it is a [Job] that has a result.
 *
 * It is created with [async][CoroutineScope.async] coroutine builder or via constructor of [CompletableDeferred] class.
 * It is in [active][isActive] state while the value is being computed.
 *
 * Deferred value has the same state machine as the [Job] with additional convenience methods to retrieve
 * successful or failed result of the computation that was carried out. The result of the deferred is
 * available when it is [completed][isCompleted] and can be retrieved by [await] method, which throws
 * exception if the deferred had failed.
 * A _failed_ deferred is considered to be [completed exceptionally][isCompletedExceptionally].
 * The corresponding exception can be retrieved via [getCompletionExceptionOrNull] from a completed instance of deferred.
 *
 * Usually, a deferred value is created in _active_ state (it is created and started).
 * However, [async][CoroutineScope.async] coroutine builder has an optional `start` parameter that creates a deferred value in _new_ state
 * when this parameter is set to [CoroutineStart.LAZY].
 * Such a deferred can be be made _active_ by invoking [start], [join], or [await].
 *
 * A deferred value is a [Job]. A job in the
 * [coroutineContext](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.coroutines.experimental/coroutine-context.html)
 * of [async][CoroutineScope.async] builder represents the coroutine itself.
 *
 * All functions on this interface and on all interfaces derived from it are **thread-safe** and can
 * be safely invoked from concurrent coroutines without external synchronization.
 */
public interface Deferred<out T> : Job {
    /**
     * Returns `true` if computation of this deferred value has _completed exceptionally_.
     * It is `true` when both [isCompleted] and [isFailed] are true.
     * It implies that [isActive] is `false`.
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
     */
    public fun getCompleted(): T

    /**
     * Returns *completion exception* result if this deferred [completed exceptionally][isCompletedExceptionally],
     * `null` if it is completed normally, or throws [IllegalStateException] if this deferred value has not
     * [completed][isCompleted] yet.
     *
     * This function is designed to be used from [invokeOnCompletion] handlers, when there is an absolute certainty that
     * the value is already complete. See also [getCompleted].
     */
    public fun getCompletionExceptionOrNull(): Throwable?

    /**
     * @suppress **Deprecated**: Use `isActive`.
     */
    @Deprecated(message = "Use `isActive`", replaceWith = ReplaceWith("isActive"))
    public val isComputing: Boolean get() = isActive
}

/**
 * Creates new coroutine and returns its future result as an implementation of [Deferred].
 * The running coroutine is cancelled when the resulting deferred is [cancelled][Job.cancel].
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * An optional [start] parameter can be set to [CoroutineStart.LAZY] to start coroutine _lazily_. In this case,,
 * the resulting [Deferred] is created in _new_ state. It can be explicitly started with [start][Job.start]
 * function and will be started implicitly on the first invocation of [join][Job.join], [await][Deferred.await] or [awaitAll].
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param onCompletion optional completion handler for the coroutine (see [Job.invokeOnCompletion]).
 * @param block the coroutine code.
 */
public fun <T> CoroutineScope.async(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    block: suspend CoroutineScope.() -> T
): Deferred<T> {
    val newContext = newCoroutineContext(context)
    val coroutine = if (start.isLazy)
        LazyDeferredCoroutine(newContext, block) else
        DeferredCoroutine<T>(newContext, active = true)
    if (onCompletion != null) coroutine.invokeOnCompletion(handler = onCompletion)
    coroutine.start(start, coroutine, block)
    return coroutine
}

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

@Suppress("UNCHECKED_CAST")
private open class DeferredCoroutine<T>(
    parentContext: CoroutineContext,
    active: Boolean
) : AbstractCoroutine<T>(parentContext, active), Deferred<T>, SelectClause1<T> {
    override fun getCompleted(): T = getCompletedInternal() as T
    override suspend fun await(): T = awaitInternal() as T
    override val onAwait: SelectClause1<T> get() = this
    override fun <R> registerSelectClause1(select: SelectInstance<R>, block: suspend (T) -> R) =
        registerSelectClause1Internal(select, block)
}

private class LazyDeferredCoroutine<T>(
    parentContext: CoroutineContext,
    private val block: suspend CoroutineScope.() -> T
) : DeferredCoroutine<T>(parentContext, active = false) {
    override fun onStart() {
        block.startCoroutineCancellable(this, this)
    }
}
