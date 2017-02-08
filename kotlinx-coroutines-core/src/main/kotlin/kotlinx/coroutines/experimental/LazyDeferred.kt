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

import java.util.concurrent.atomic.AtomicIntegerFieldUpdater
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

/**
 * Lazy deferred value is conceptually a non-blocking cancellable future that is started on
 * the first [await] or [start] invocation.
 * It is created with [lazyDefer] coroutine builder.
 *
 * Unlike a simple [Deferred] value, a lazy deferred value has five states:
 *
 * * _Pending_ (initial, _active_ state before the starts of the coroutine) --
 *   [isActive] `true`, but [isComputing] `false`,
 *   [isCompletedExceptionally] `false`, and [isCancelled] `false`.
 * * _Computing_ (intermediate state while computing the value) --
 *   [isActive] `true`, [isComputing] `true`,
 *   [isCompletedExceptionally] `false`, and [isCancelled] `false`.
 * * _Computed_ (final _completed_ state) -- [isActive] `false`, [isComputing] `false`,
 *   [isCompletedExceptionally] `false`, [isCancelled] `false`.
 * * _Failed_ (final _completed_ state) -- [isActive] `false`, [isComputing] `false`,
 *   [isCompletedExceptionally] `true`, [isCancelled] `false`.
 * * _Canceled_ (final _completed_ state) -- [isActive] `false`, [isComputing] `false`,
 *   [isCompletedExceptionally] `true`, [isCancelled] `true`.
 *
 * If this lazy deferred value is [cancelled][cancel], then it becomes immediately complete and
 * cancels ongoing computation coroutine if it was started.
 */
public interface LazyDeferred<out T> : Deferred<T> {
    /**
     * Returns `true` if the coroutine is computing its value.
     */
    public val isComputing: Boolean

    /**
     * Starts coroutine to compute this lazily deferred value. The result `true` if this invocation actually
     * started coroutine or `false` if it was already started or cancelled.
     */
    public fun start(): Boolean
}

/**
 * Lazily starts new coroutine on the first [await][Deferred.await] or [start][LazyDeferred.start] invocation
 * on the resulting [LazyDeferred].
 * The running coroutine is cancelled when the resulting value is [cancelled][Job.cancel].
 *
 * The [context] for the new coroutine must be explicitly specified.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 */
public fun <T> lazyDefer(context: CoroutineContext, block: suspend CoroutineScope.() -> T) : LazyDeferred<T> =
    LazyDeferredCoroutine(newCoroutineContext(context), block).apply {
        initParentJob(context[Job])
    }

private class LazyDeferredCoroutine<T>(
    context: CoroutineContext,
    val block: suspend CoroutineScope.() -> T
) : DeferredCoroutine<T>(context), LazyDeferred<T> {

    @Volatile
    var lazyState: Int = STATE_PENDING

    companion object {
        private val STATE_PENDING = 0
        private val STATE_COMPUTING = 1
        private val STATE_COMPLETE = 2

        private val LAZY_STATE: AtomicIntegerFieldUpdater<LazyDeferredCoroutine<*>> =
            AtomicIntegerFieldUpdater.newUpdater(LazyDeferredCoroutine::class.java, "lazyState")
    }

    /*
        === State linking & linearization of the overall state ===

        There are two state variables in this object and they have to update atomically from the standpoint of
        external observer:
            1. Job.state that is used by isActive function.
            2. lazyState that is used to make sure coroutine starts at most once.
        External observer must see only three states, not four, i.e. it should not be able
        to see `isActive == false`, but `isComputing == true`.

        On completion/cancellation state variables are updated in this order:
            a) state <- complete (isComplete starts returning true)
            b) lazyState <- STATE_COMPLETE (see onStateUpdate)
        This is why, `isComputing` checks state variables in reverse order:
            a) lazyState is checked _first_
            b) isActive is checked after it
        This way cancellation/completion is atomic w.r.t to all state functions.

        `start` function also has to check lazyState _before_ isActive.
     */

    override val isComputing: Boolean get() = lazyState == STATE_COMPUTING && isActive

    override fun start(): Boolean {
        while (true) { // lock-free loop on lazyState
            when (lazyState) { // volatile read
                STATE_PENDING -> {
                    if (isActive) { // then volatile read Job.state (inside isActive)
                        // can try to start
                        if (LAZY_STATE.compareAndSet(this, STATE_PENDING, STATE_COMPUTING)) {
                            block.startCoroutine(this, this)
                            return true
                        }
                    } else {
                        // cannot start -- already complete -- help update lazyState
                        lazyState = STATE_COMPLETE
                        return false
                    }
                }
                else -> return false
            }
        }
    }

    override fun onStateUpdate(update: Any?) {
        lazyState = STATE_COMPLETE
    }
}
