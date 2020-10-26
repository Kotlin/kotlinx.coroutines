/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("DEPRECATION_ERROR")

package kotlinx.coroutines

import kotlinx.coroutines.selects.*

/**
 * A [Deferred] that can be completed via public functions [complete] or [cancel][Job.cancel].
 *
 * Note that the [complete] function returns `false` when this deferred value is already complete or completing,
 * while [cancel][Job.cancel] returns `true` as long as the deferred is still _cancelling_ and the corresponding
 * exception is incorporated into the final [completion exception][getCompletionExceptionOrNull].
 *
 * An instance of completable deferred can be created by `CompletableDeferred()` function in _active_ state.
 *
 * All functions on this interface are **thread-safe** and can
 * be safely invoked from concurrent coroutines without external synchronization.
 *
 * **The `CompletableDeferred` interface is not stable for inheritance in 3rd party libraries**,
 * as new methods might be added to this interface in the future, but is stable for use.
 */
public interface CompletableDeferred<T> : Deferred<T> {
    /**
     * Completes this deferred value with a given [value]. The result is `true` if this deferred was
     * completed as a result of this invocation and `false` otherwise (if it was already completed).
     *
     * Subsequent invocations of this function have no effect and always produce `false`.
     *
     * This function transitions this deferred into _completed_ state if it was not completed or cancelled yet.
     * However, if this deferred has children, then it transitions into _completing_ state and becomes _complete_
     * once all its children are [complete][isCompleted]. See [Job] for details.
     */
    public fun complete(value: T): Boolean

    /**
     * Completes this deferred value exceptionally with a given [exception]. The result is `true` if this deferred was
     * completed as a result of this invocation and `false` otherwise (if it was already completed).
     *
     * Subsequent invocations of this function have no effect and always produce `false`.
     *
     * This function transitions this deferred into _cancelled_ state if it was not completed or cancelled yet.
     * However, that if this deferred has children, then it transitions into _cancelling_ state and becomes _cancelled_
     * once all its children are [complete][isCompleted]. See [Job] for details.
     */
    public fun completeExceptionally(exception: Throwable): Boolean
}

/**
 * Completes this deferred value with the value or exception in the given [result]. Returns `true` if this deferred
 * was completed as a result of this invocation and `false` otherwise (if it was already completed).
 *
 * Subsequent invocations of this function have no effect and always produce `false`.
 *
 * This function transitions this deferred in the same ways described by [CompletableDeferred.complete] and
 * [CompletableDeferred.completeExceptionally].
 */
public fun <T> CompletableDeferred<T>.completeWith(result: Result<T>): Boolean =
    result.fold({ complete(it) }, { completeExceptionally(it) })

/**
 * Creates a [CompletableDeferred] in an _active_ state.
 * It is optionally a child of a [parent] job.
 */
@Suppress("FunctionName")
public fun <T> CompletableDeferred(parent: Job? = null): CompletableDeferred<T> = CompletableDeferredImpl(parent)

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
