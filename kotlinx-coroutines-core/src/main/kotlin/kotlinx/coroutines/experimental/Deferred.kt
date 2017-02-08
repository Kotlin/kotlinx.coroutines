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

import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

/**
 * Deferred value is conceptually a non-blocking cancellable future.
 * It is created with [defer] coroutine builder.
 * It is in [active][isActive] state while the value is being computed.
 *
 * Deferred value has four states:
 *
 * * _Active_ (initial state) -- [isActive] `true`, [isCompletedExceptionally] `false`,
 *   and [isCancelled] `false`.
 *   Both [getCompleted] and [getCompletionException] throw [IllegalStateException].
 * * _Computed_ (final _completed_ state) -- [isActive] `false`,
 *   [isCompletedExceptionally] `false`, [isCancelled] `false`.
 * * _Failed_ (final _completed_ state) -- [isActive] `false`,
 *   [isCompletedExceptionally] `true`, [isCancelled] `false`.
 * * _Canceled_ (final _completed_ state) -- [isActive] `false`,
 *   [isCompletedExceptionally] `true`, [isCancelled] `true`.
 */
public interface Deferred<out T> : Job {
    /**
     * Returns `true` if computation of this deferred value has _completed exceptionally_ -- it had
     * either _failed_ with exception during computation or was [cancelled][cancel].
     * It implies that [isActive] is `false`.
     */
    val isCompletedExceptionally: Boolean

    /**
     * Returns `true` if computation of this deferred value was [cancelled][cancel].
     * It implies that [isActive] is `false` and [isCompletedExceptionally] is `true`.
     */
    val isCancelled: Boolean

    /**
     * Awaits for completion of this value without blocking a thread and resumes when deferred computation is complete.
     * This suspending function is cancellable.
     * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
     * immediately resumes with [CancellationException].
     */
    public suspend fun await(): T

    /**
     * Returns *completed* result or throws [IllegalStateException] if this deferred value is still [isActive].
     * It throws the corresponding exception if this deferred has completed exceptionally.
     * This function is designed to be used from [onCompletion] handlers, when there is an absolute certainty that
     * the value is already complete.
     */
    public fun getCompleted(): T
}

/**
 * Starts new coroutine and returns its result as an implementation of [Deferred].
 * The running coroutine is cancelled when the resulting object is [cancelled][Job.cancel].
 *
 * The [context] for the new coroutine must be explicitly specified.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 */
public fun <T> defer(context: CoroutineContext, block: suspend CoroutineScope.() -> T) : Deferred<T> =
    DeferredCoroutine<T>(newCoroutineContext(context)).apply {
        initParentJob(context[Job])
        block.startCoroutine(this, this)
    }

internal open class DeferredCoroutine<T>(
    context: CoroutineContext
) : AbstractCoroutine<T>(context), Deferred<T> {
    protected open fun start(): Boolean = false // LazyDeferredCoroutine overrides

    override val isCompletedExceptionally: Boolean get() = getState() is CompletedExceptionally
    override val isCancelled: Boolean get() = getState() is Cancelled

    @Suppress("UNCHECKED_CAST")
    suspend override fun await(): T {
        // quick check if already complete (avoid extra object creation)
        getState().let { state ->
            if (state !is Active) {
                if (state is CompletedExceptionally) throw state.exception
                return state as T
            }
        }
        if (start()) { // LazyDeferredCoroutine overrides
            // recheck state (may have started & already completed
            getState().let { state ->
                if (state !is Active) {
                    if (state is CompletedExceptionally) throw state.exception
                    return state as T
                }
            }
        }
        // Note: await is cancellable itself!
        return awaitGetValue()
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun awaitGetValue(): T = suspendCancellableCoroutine { cont ->
        cont.unregisterOnCompletion(onCompletion {
            val state = getState()
            check(state !is Active)
            if (state is CompletedExceptionally)
                cont.resumeWithException(state.exception)
            else
                cont.resume(state as T)
        })
    }

    @Suppress("UNCHECKED_CAST")
    override fun getCompleted(): T {
        val state = getState()
        check(state !is Active) { "This deferred value is still active" }
        if (state is CompletedExceptionally) throw state.exception
        return state as T
    }

    // for nicer debugging
    override fun toString(): String = "${javaClass.simpleName}{" +
        (if (isActive) "isActive=true" else "completed=${getState()}") + "}"
}
