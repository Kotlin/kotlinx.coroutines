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

import kotlinx.coroutines.experimental.selects.SelectInstance

/**
 * Concrete implementation of [Deferred] that can be completed via public functions
 * [complete], [completeExceptionally], and [cancel].
 *
 * Completion functions return `false` when this deferred value is already complete.
 */
@Suppress("UNCHECKED_CAST")
public class CompletableDeferred<T> : JobSupport(true), Deferred<T> {
    override fun getCompleted(): T = getCompletedInternal() as T
    suspend override fun await(): T = awaitInternal() as T
    override fun <R> registerSelectAwait(select: SelectInstance<R>, block: suspend (T) -> R) =
        registerSelectAwaitInternal(select, block as (suspend (Any?) -> R))

    /**
     * Completes this deferred value with a given [value]. The result is `true` if this deferred was
     * completed as a result of this invocation and `false` otherwise (if it was already completed).
     *
     * Repeated invocations of this function have no effect and always produce `false`.
     */
    public fun complete(value: T): Boolean {
        while (true) { // lock-free loop on state
            val state = this.state // atomic read
            when (state) {
                is Incomplete -> {
                    // actually, we don't care about the mode here at all, so just use a default
                    if (updateState(state, value, mode = MODE_ATOMIC_DEFAULT))
                        return true
                }
                else -> return false
            }
        }
    }

    /**
     * Completes this deferred value exceptionally with a given [exception]. The result is `true` if this deferred was
     * completed as a result of this invocation and `false` otherwise (if it was already completed).
     *
     * Repeated invocations of this function have no effect and always produce `false`.
     */
    public fun completeExceptionally(exception: Throwable): Boolean {
        while (true) { // lock-free loop on state
            val state = this.state // atomic read
            when (state) {
                is Incomplete -> {
                    // actually, we don't care about the mode here at all, so just use a default
                    if (updateState(state, CompletedExceptionally(exception), mode = MODE_ATOMIC_DEFAULT))
                        return true
                }
                else -> return false
            }
        }
    }
}