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

/**
 * A [Deferred] that can be completed via public functions
 * [complete], [completeExceptionally], and [cancel].
 *
 * Completion functions return `false` when this deferred value is already complete.
 *
 * A completable deferred value has the following states:
 *
 * | **State**                 | [isActive] | [isCompleted] | [isCompletedExceptionally] | [isCancelled] |
 * | ------------------------- | ---------- | ------------- | -------------------------- | ------------- |
 * | _Active_ (initial state)  | `true`     | `false`       | `false`                    | `false`       |
 * | _Cancelled_ (final state) | `false`    | `true`        | `true`                     | `true`        |
 * | _Resolved_  (final state) | `false`    | `true`        | `false`                    | `false`       |
 * | _Failed_    (final state) | `false`    | `true`        | `true`                     | `false`       |
 *
 * A an instance of completable deferred can be created by `CompletableDeferred()` function in _active_ state.
 *
 *  ```
 *  +--------+   complete   +-----------+
 *  | Active | ---------+-> | Resolved  |
 *  +--------+          |   |(completed)|
 *       |              |   +-----------+
 *       | cancel       |
 *       V              |   +-----------+
 *  +-----------+       +-> |  Failed   |
 *  | Cancelled |           |(completed)|
 *  |(completed)|           +-----------+
 *  +-----------+
 * ```
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
    override fun getCompleted(): T = getCompletedInternal() as T
    override suspend fun await(): T = awaitInternal() as T

    override fun complete(value: T): Boolean = when (state) {
        is Incomplete -> {
            // actually, we don't care about the mode here at all, so just use a default
            updateState(value, mode = MODE_ATOMIC_DEFAULT)
            true
        }
        else -> false
    }

    override fun completeExceptionally(exception: Throwable): Boolean = when (state) {
        is Incomplete -> {
            // actually, we don't care about the mode here at all, so just use a default
            updateState(CompletedExceptionally(exception), mode = MODE_ATOMIC_DEFAULT)
            true
        }
        else -> false
    }
}
