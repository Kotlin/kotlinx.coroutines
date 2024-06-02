package kotlinx.coroutines

import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*

/**
 * Defines start options for coroutines builders.
 *
 * It is used in the `start` parameter of coroutine builder functions like
 * [launch][CoroutineScope.launch] and [async][CoroutineScope.async]
 * to describe when and how the coroutine should be dispatched initially.
 *
 * This parameter only affects how the coroutine behaves until it reaches the first suspension point.
 * After that, cancellability and dispatching depend on the implementation details of the invoked suspending functions.
 * Use [suspendCancellableCoroutine] to implement custom cancellable suspending functions.
 *
 * The summary of coroutine start options is:
 * - [DEFAULT] immediately schedules the coroutine for execution according to its context;
 * - [LAZY] starts coroutine lazily, only when it is needed;
 * - [ATOMIC] atomically (in a non-cancellable way) schedules the coroutine for execution according to its context;
 * - [UNDISPATCHED] immediately executes the coroutine until its first suspension point _in the current thread_.
 */
public enum class CoroutineStart {
    /**
     * Immediately schedules the coroutine for execution according to its context. This is usually the default option.
     *
     * The behavior of [DEFAULT] depends on the result of [CoroutineDispatcher.isDispatchNeeded] in
     * the context of the started coroutine.
     * - In the typical case where a dispatch is needed, the coroutine is dispatched for execution on that dispatcher.
     *   It may take a while for the dispatcher to start the task; the thread that invoked the coroutine builder
     *   does not wait for the task to start and instead continues its execution.
     * - If no dispatch is needed (which is the case for [Dispatchers.Main.immediate][MainCoroutineDispatcher.immediate]
     *   when already on the main thread and for [Dispatchers.Unconfined]),
     *   the task is executed immediately in the same thread that invoked the coroutine builder,
     *   similarly to [UNDISPATCHED].
     *
     * If the coroutine's [Job] is cancelled before it started executing, then it will not start its
     * execution at all, and will instead complete with an exception.
     *
     * Comparisons with the other options:
     * - [LAZY] delays the moment of the initial dispatch until the completion of the coroutine is awaited.
     * - [ATOMIC] prevents the coroutine from being cancelled before its first suspension point.
     * - [UNDISPATCHED] always executes the coroutine until the first suspension immediately in the same thread
     *   (as if [CoroutineDispatcher.isDispatchNeeded] returned `false`),
     *   and also, like [ATOMIC], it ensures that the coroutine cannot be cancelled before it starts executing.
     *
     * Examples:
     *
     * ```
     * // Example of starting a new coroutine that goes through a dispatch
     * runBlocking {
     *     println("1. About to start a new coroutine.")
     *     // Dispatch the job to execute later.
     *     // The parent coroutine's dispatcher is inherited by default.
     *     // In this case, it's the single thread backing `runBlocking`.
     *     val job = launch {
     *         println("3. When the thread is available, we start the coroutine")
     *     }
     *     println("2. The thread keeps doing other work after launching the coroutine")
     * }
     * ```
     *
     * ```
     * // Example of starting a new coroutine that doesn't go through a dispatch initially
     * runBlocking {
     *     println("1. About to start a coroutine not needing a dispatch.")
     *     // Dispatch the job to execute.
     *     // `Dispatchers.Unconfined` is explicitly chosen.
     *     val job = launch(Dispatchers.Unconfined) {
     *         println("2. The body will be executed immediately")
     *         delay(50.milliseconds) // give up the thread to the outer coroutine
     *         println("4. When the thread is next available, this coroutine proceeds further")
     *     }
     *     println("3. After the initial suspension, the thread does other work.")
     * }
     * ```
     *
     * ```
     * // Example of cancelling coroutines before they start executing.
     * runBlocking {
     *     launch { // dispatches the job to execute on this thread later
     *         println("This code will never execute")
     *     }
     *     cancel() // cancels the current coroutine scope and its children
     *     launch(Dispatchers.Unconfined) {
     *         println("This code will never execute")
     *     }
     *     println("This code will execute.")
     * }
     * ```
     */
    DEFAULT,

    /**
     * Starts the coroutine lazily, only when it is needed.
     *
     * Starting a coroutine with [LAZY] only creates the coroutine, but does not schedule it for execution.
     * When the completion of the coroutine is first awaited
     * (for example, via [Job.join]) or explicitly [started][Job.start],
     * the dispatch procedure described in [DEFAULT] happens in the thread that did it.
     *
     * The details of what counts as waiting can be found in the documentation of the corresponding coroutine builders
     * like [launch][CoroutineScope.launch] and [async][CoroutineScope.async].
     *
     * If the coroutine's [Job] is cancelled before it started executing, then it will not start its
     * execution at all, and will instead complete with an exception.
     *
     * **Pitfall**: launching a coroutine with [LAZY] without awaiting or cancelling it at any point means that it will
     * never be completed, leading to deadlocks and resource leaks.
     * For example, the following code will deadlock, since [coroutineScope] waits for all of its child coroutines to
     * complete:
     * ```
     * coroutineScope {
     *     launch(start = CoroutineStart.LAZY) { }
     * }
     * ```
     *
     * Examples:
     *
     * ```
     * // Example of lazily starting a new coroutine that goes through a dispatch
     * runBlocking {
     *     println("1. About to start a new coroutine.")
     *     // Create a job to execute on `Dispatchers.Default` later.
     *     val job = launch(Dispatchers.Default, start = CoroutineStart.LAZY) {
     *         println("3. Only now does the coroutine start.")
     *     }
     *     delay(10.milliseconds) // try to give the coroutine some time to run
     *     println("2. The coroutine still has not started. Now, we await it.")
     *     job.join()
     * }
     * ```
     *
     * ```
     * // Example of lazily starting a new coroutine that doesn't go through a dispatch initially
     * runBlocking {
     *     println("1. About to lazily start a new coroutine.")
     *     // Create a job to execute on `Dispatchers.Unconfined` later.
     *     val lazyJob = launch(Dispatchers.Unconfined, start = CoroutineStart.LAZY) {
     *         println("3. The coroutine starts on the thread that called `join`.")
     *     }
     *     // We start the job on another thread for illustrative purposes
     *     launch(Dispatchers.Default) {
     *         println("2. We start the lazyJob.")
     *         job.start() // runs lazyJob's code in-place
     *         println("4. Only now does the `start` call return.")
     *     }
     * }
     * ```
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
