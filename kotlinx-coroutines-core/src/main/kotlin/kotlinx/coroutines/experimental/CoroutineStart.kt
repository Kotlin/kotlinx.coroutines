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

import kotlinx.coroutines.experimental.intrinsics.startCoroutineUndispatched
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.startCoroutine

/**
 * Defines start option for coroutines builders.
 * It is used in `start` parameter of [launch], [async], and [actor][kotlinx.coroutines.experimental.channels.actor]
 * coroutine builder functions.
 */
public enum class CoroutineStart {
    /**
     * Default -- schedules coroutine for execution according to its context.
     *
     * If the [CoroutineDispatcher] of the coroutine context returns `true` from [CoroutineDispatcher.isDispatchNeeded]
     * function as most dispatchers do, then the coroutine code is dispatched for execution later, while the code that
     * invoked the coroutine builder continues execution.
     *
     * Note, that [Unconfined] dispatcher always returns `false` from its [CoroutineDispatcher.isDispatchNeeded]
     * function, so starting coroutine with [Unconfined] dispatcher by [DEFAULT] is the same as using [UNDISPATCHED].
     */
    DEFAULT,

    /**
     * Starts coroutine lazily, only when it is needed.
     *
     * See the documentation for the corresponding coroutine builders for details:
     * [launch], [async], and [actor][kotlinx.coroutines.experimental.channels.actor].
     */
    LAZY,

    /**
     * Immediately executes coroutine until its first suspension point _in the current thread_ as if it the
     * coroutine was started using [Unconfined] dispatcher. However, when coroutine is resumed from suspension
     * it is dispatched according to the [CoroutineDispatcher] in its context.
     */
    UNDISPATCHED;

    /**
     * Starts the corresponding block as a coroutine with this coroutine start strategy.
     *
     * * [DEFAULT] uses [startCoroutine].
     * * [UNDISPATCHED] uses [startCoroutineUndispatched].
     * * [LAZY] does nothing.
     */
    public operator fun <R, T> invoke(block: suspend R.() -> T, receiver: R, completion: Continuation<T>) =
        when (this) {
            CoroutineStart.DEFAULT -> block.startCoroutine(receiver, completion)
            CoroutineStart.UNDISPATCHED -> block.startCoroutineUndispatched(receiver, completion)
            CoroutineStart.LAZY -> Unit // will start lazily
        }

    /**
     * Returns `true` when [LAZY].
     */
    public val isLazy: Boolean get() = this === LAZY
}
