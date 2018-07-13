/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.selects.*

/**
 * A [Deferred] that can be completed via public functions [complete] or [cancel][Job.cancel].
 *
 * Note, that [complete] functions returns `false` when this deferred value is already complete or completing,
 * while [cancel][Job.cancel] returns `true` as long the deferred is still _cancelling_ and the corresponding
 * exception is incorporated into the final [completion exception][getCompletionExceptionOrNull].
 *
 * An instance of completable deferred can be created by `CompletableDeferred()` function in _active_ state.
 *
 * All functions on this interface and on all interfaces derived from it are **thread-safe** and can
 * be safely invoked from concurrent coroutines without external synchronization.
 */
public interface CompletableDeferred<T> : Deferred<T> {
    /**
     * Completes this deferred value with a given [value]. The result is `true` if this deferred was
     * completed as a result of this invocation and `false` otherwise (if it was already completed).
     *
     * Repeated invocations of this function have no effect and always produce `false`.
     */
    public fun complete(value: T): Boolean

    /**
     * Completes this deferred value exceptionally with a given [exception]. The result is `true` if this deferred was
     * completed as a result of this invocation and `false` otherwise (if it was already completed).
     *
     * Repeated invocations of this function have no effect and always produce `false`.
     */
    @Deprecated(message = "Use cancel", replaceWith = ReplaceWith("cancel(exception)"))
    public fun completeExceptionally(exception: Throwable): Boolean
}

/**
 * Creates a [CompletableDeferred] in an _active_ state.
 * It is optionally a child of a [parent] job.
 */
@Suppress("FunctionName")
public fun <T> CompletableDeferred(parent: Job? = null): CompletableDeferred<T> = CompletableDeferredImpl(parent)

/** @suppress **Deprecated:** Binary compatibility only */
@Deprecated(message = "Binary compatibility only", level = DeprecationLevel.HIDDEN)
@Suppress("FunctionName")
public fun <T> CompletableDeferred(): CompletableDeferred<T> = CompletableDeferredImpl(null)

/**
 * Creates an already _completed_ [CompletableDeferred] with a given [value].
 */
@Suppress("FunctionName")
public fun <T> CompletableDeferred(value: T): CompletableDeferred<T> = CompletableDeferredImpl<T>(null).apply { complete(value) }

/**
 * Concrete implementation of [CompletableDeferred].
 */
@Suppress("UNCHECKED_CAST")
private class CompletableDeferredImpl<T>(
    parent: Job?
) : JobSupport(true), CompletableDeferred<T>, SelectClause1<T> {
    init { initParentJobInternal(parent) }
    override val cancelsParent: Boolean get() = true
    override val onCancelComplete get() = true
    override fun getCompleted(): T = getCompletedInternal() as T
    override suspend fun await(): T = awaitInternal() as T
    override val onAwait: SelectClause1<T> get() = this
    override fun <R> registerSelectClause1(select: SelectInstance<R>, block: suspend (T) -> R) =
        registerSelectClause1Internal(select, block)

    override fun complete(value: T): Boolean =
        makeCompleting(value)
    override fun completeExceptionally(exception: Throwable): Boolean =
        makeCompleting(CompletedExceptionally(exception))
}
