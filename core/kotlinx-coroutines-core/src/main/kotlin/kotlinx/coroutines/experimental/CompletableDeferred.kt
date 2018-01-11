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

/**
 * A [Deferred] that can be completed via public functions
 * [complete], [completeExceptionally], and [cancel].
 *
 * Completion functions return `false` when this deferred value is already complete or completing.
 *
 * An instance of completable deferred can be created by `CompletableDeferred()` function in _active_ state.
 *
 * All functions on this interface and on all interfaces derived from it are **thread-safe** and can
 * be safely invoked from concurrent coroutines without external synchronization.
 */
public actual interface CompletableDeferred<T> : Deferred<T> {
    /**
     * Completes this deferred value with a given [value]. The result is `true` if this deferred was
     * completed as a result of this invocation and `false` otherwise (if it was already completed).
     *
     * Repeated invocations of this function have no effect and always produce `false`.
     */
    public actual fun complete(value: T): Boolean

    /**
     * Completes this deferred value exceptionally with a given [exception]. The result is `true` if this deferred was
     * completed as a result of this invocation and `false` otherwise (if it was already completed).
     *
     * Repeated invocations of this function have no effect and always produce `false`.
     */
    public actual fun completeExceptionally(exception: Throwable): Boolean
}

/**
 * Creates a [CompletableDeferred] in an _active_ state.
 * It is optionally a child of a [parent] job.
 */
@Suppress("FunctionName")
public actual fun <T> CompletableDeferred(parent: Job? = null): CompletableDeferred<T> = CompletableDeferredImpl(parent)

/** @suppress **Deprecated:** Binary compatibility only */
@Deprecated(message = "Binary compatibility only", level = DeprecationLevel.HIDDEN)
@Suppress("FunctionName")
public fun <T> CompletableDeferred(): CompletableDeferred<T> = CompletableDeferredImpl(null)

/**
 * Creates an already _completed_ [CompletableDeferred] with a given [value].
 */
@Suppress("FunctionName")
public actual fun <T> CompletableDeferred(value: T): CompletableDeferred<T> = CompletableDeferredImpl<T>(null).apply { complete(value) }

/**
 * Concrete implementation of [CompletableDeferred].
 */
@Suppress("UNCHECKED_CAST")
private class CompletableDeferredImpl<T>(
    parent: Job?
) : JobSupport(true), CompletableDeferred<T> {
    init { initParentJob(parent) }
    override val onCancelMode: Int get() = ON_CANCEL_MAKE_COMPLETING

    override fun getCompleted(): T = getCompletedInternal() as T
    override suspend fun await(): T = awaitInternal() as T
    override val onAwait: SelectClause1<T>
        get() = this as SelectClause1<T>

    override fun complete(value: T): Boolean =
        makeCompleting(value)

    override fun completeExceptionally(exception: Throwable): Boolean =
        makeCompleting(CompletedExceptionally(exception))
}
