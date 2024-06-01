package kotlinx.coroutines

import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*

/**
 * Defines start options for coroutines builders.
 *
 * It is used in `start` parameter of [launch][CoroutineScope.launch], [async][CoroutineScope.async], and other coroutine builder functions.
 *
 * This parameter only affects how the coroutine behaves until it reaches the first suspension point.
 * After that, cancellability and dispatching depend on the implementation details of the invoked suspending functions.
 * Use [suspendCancellableCoroutine] to implement custom cancellable suspending functions.
 *
 * The summary of coroutine start options is:
 * - [DEFAULT] -- immediately schedules coroutine for execution according to its context;
 * - [LAZY] -- starts coroutine lazily, only when it is needed;
 * - [ATOMIC] -- atomically (in a non-cancellable way) schedules coroutine for execution according to its context;
 * - [UNDISPATCHED] -- immediately executes coroutine until its first suspension point _in the current thread_.
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
     * The coroutine started with [ATOMIC] is guaranteed to start execution even if its [Job] was cancelled.
     * This [CoroutineStart] option can be used to ensure resources' disposal in case of cancellation.
     * For example, this `producer` guarantees that the `channel` will be eventually closed,
     * even if the coroutine scope is cancelled before `producer` is called:
     * ```
     * fun CoroutineScope.producer(channel: SendChannel<Int>) =
     *     launch(start = CoroutineStart.ATOMIC) {
     *         try {
     *             // produce elements
     *         } finally {
     *             channel.close()
     *         }
     *     }
     * ```
     *
     * This is a **delicate** API. The coroutine starts execution even if its [Job] is cancelled before starting.
     * However, the resources used within a coroutine may rely on the cancellation mechanism,
     * and cannot be used after the [Job] cancellation. For instance, in Android development, updating a UI element
     * is not allowed if the coroutine's scope, which is tied to the element's lifecycle, has been cancelled.
     */
    @DelicateCoroutinesApi
    ATOMIC,

    /**
     * Immediately executes the coroutine until its first suspension point _in the current thread_ similarly to
     * the coroutine being started using [Dispatchers.Unconfined]. However, when the coroutine is resumed from suspension
     * it is dispatched according to the [CoroutineDispatcher] in its context.
     *
     * This is similar to [ATOMIC] in the sense that coroutine starts executing even if it was already cancelled,
     * but the difference is that it starts executing in the same thread.
     *
     * ### Unconfined event loop
     *
     * Unlike [Dispatchers.Unconfined] and [MainCoroutineDispatcher.immediate], nested undispatched coroutines do not form
     * an event loop that otherwise prevents potential stack overflow in case of unlimited nesting.
     */
    UNDISPATCHED;

    /**
     * Starts the corresponding block with receiver as a coroutine with this coroutine start strategy.
     *
     * - [DEFAULT] uses [startCoroutineCancellable].
     * - [ATOMIC] uses [startCoroutine].
     * - [UNDISPATCHED] uses [startCoroutineUndispatched].
     * - [LAZY] does nothing.
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
