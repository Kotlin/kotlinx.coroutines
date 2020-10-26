/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("NO_EXPLICIT_VISIBILITY_IN_API_MODE")
package kotlinx.coroutines

import kotlinx.coroutines.CoroutineStart.*
import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*

/**
 * Defines start options for coroutines builders.
 * It is used in `start` parameter of [launch][CoroutineScope.launch], [async][CoroutineScope.async], and other coroutine builder functions.
 *
 * The summary of coroutine start options is:
 * * [DEFAULT] -- immediately schedules coroutine for execution according to its context;
 * * [LAZY] -- starts coroutine lazily, only when it is needed;
 * * [ATOMIC] -- atomically (in a non-cancellable way) schedules coroutine for execution according to its context;
 * * [UNDISPATCHED] -- immediately executes coroutine until its first suspension point _in the current thread_.
 */
public enum class CoroutineStart {
    /**
     * Default -- immediately schedules the coroutine for execution according to its context.
     *
     * If the [CoroutineDispatcher] of the coroutine context returns `true` from [CoroutineDispatcher.isDispatchNeeded]
     * function as most dispatchers do, then the coroutine code is dispatched for execution later, while the code that
     * invoked the coroutine builder continues execution.
     *
     * Note that [Dispatchers.Unconfined] always returns `false` from its [CoroutineDispatcher.isDispatchNeeded]
     * function, so starting a coroutine with [Dispatchers.Unconfined] by [DEFAULT] is the same as using [UNDISPATCHED].
     *
     * If coroutine [Job] is cancelled before it even had a chance to start executing, then it will not start its
     * execution at all, but will complete with an exception.
     *
     * Cancellability of a coroutine at suspension points depends on the particular implementation details of
     * suspending functions. Use [suspendCancellableCoroutine] to implement cancellable suspending functions.
     */
    DEFAULT,

    /**
     * Starts the coroutine lazily, only when it is needed.
     *
     * See the documentation for the corresponding coroutine builders for details
     * (like [launch][CoroutineScope.launch] and [async][CoroutineScope.async]).
     *
     * If coroutine [Job] is cancelled before it even had a chance to start executing, then it will not start its
     * execution at all, but will complete with an exception.
     */
    LAZY,

    /**
     * Atomically (i.e., in a non-cancellable way) schedules the coroutine for execution according to its context.
     * This is similar to [DEFAULT], but the coroutine cannot be cancelled before it starts executing.
     *
     * Cancellability of coroutine at suspension points depends on the particular implementation details of
     * suspending functions as in [DEFAULT].
     */
    @ExperimentalCoroutinesApi // Since 1.0.0, no ETA on stability
    ATOMIC,

    /**
     * Immediately executes the coroutine until its first suspension point _in the current thread_ as if the
     * coroutine was started using [Dispatchers.Unconfined]. However, when the coroutine is resumed from suspension
     * it is dispatched according to the [CoroutineDispatcher] in its context.
     *
     * This is similar to [ATOMIC] in the sense that coroutine starts executing even if it was already cancelled,
     * but the difference is that it starts executing in the same thread.
     *
     * Cancellability of coroutine at suspension points depends on the particular implementation details of
     * suspending functions as in [DEFAULT].
     *
     * **Note: This is an experimental api.** Execution semantics of coroutines may change in the future when this mode is used.
     */
    @ExperimentalCoroutinesApi  // Since 1.0.0, no ETA on stability
    UNDISPATCHED;

    /**
     * Starts the corresponding block as a coroutine with this coroutine's start strategy.
     *
     * * [DEFAULT] uses [startCoroutineCancellable].
     * * [ATOMIC] uses [startCoroutine].
     * * [UNDISPATCHED] uses [startCoroutineUndispatched].
     * * [LAZY] does nothing.
     *
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    public operator fun <T> invoke(block: suspend () -> T, completion: Continuation<T>): Unit =
        when (this) {
            DEFAULT -> block.startCoroutineCancellable(completion)
            ATOMIC -> block.startCoroutine(completion)
            UNDISPATCHED -> block.startCoroutineUndispatched(completion)
            LAZY -> Unit // will start lazily
        }

    /**
     * Starts the corresponding block with receiver as a coroutine with this coroutine start strategy.
     *
     * * [DEFAULT] uses [startCoroutineCancellable].
     * * [ATOMIC] uses [startCoroutine].
     * * [UNDISPATCHED] uses [startCoroutineUndispatched].
     * * [LAZY] does nothing.
     *
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    public operator fun <R, T> invoke(block: suspend R.() -> T, receiver: R, completion: Continuation<T>): Unit =
        when (this) {
            DEFAULT -> block.startCoroutineCancellable(receiver, completion)
            ATOMIC -> block.startCoroutine(receiver, completion)
            UNDISPATCHED -> block.startCoroutineUndispatched(receiver, completion)
            LAZY -> Unit // will start lazily
        }

    /**
     * Returns `true` when [LAZY].
     *
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    public val isLazy: Boolean get() = this === LAZY
}
