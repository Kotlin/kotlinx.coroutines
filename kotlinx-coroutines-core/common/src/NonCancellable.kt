@file:Suppress("DEPRECATION_ERROR")

package kotlinx.coroutines

import kotlinx.coroutines.selects.*
import kotlin.coroutines.*

/**
 * A non-cancelable job that is always [active][Job.isActive]. It is designed for [withContext] function
 * to prevent cancellation of code blocks that need to be executed without cancellation.
 *
 * Use it like this:
 * ```
 * withContext(NonCancellable) {
 *     // this code will not be cancelled
 * }
 * ```
 *
 * **WARNING**: This object is not designed to be used with [launch], [async], and other coroutine builders.
 * if you write `launch(NonCancellable) { ... }` then not only the newly launched job will not be cancelled
 * when the parent is cancelled, the whole parent-child relation between parent and child is severed.
 * The parent will not wait for the child's completion, nor will be cancelled when the child crashed.
 *
 * ## Pitfalls
 *
 * ### Overriding the exception with a [CancellationException] in a finalizer
 *
 * #### Combining [NonCancellable] with a [ContinuationInterceptor]
 *
 * The typical usage of [NonCancellable] is to ensure that cleanup code is executed even if the parent job is cancelled.
 * Example:
 *
 * ```
 * try {
 *     // some code using a resource
 * } finally {
 *     withContext(NonCancellable) {
 *         // cleanup code that should not be cancelled
 *     }
 * }
 * ```
 *
 * However, it is easy to get this pattern wrong if the cleanup code needs to run on some specific dispatcher:
 *
 * ```
 * // DO NOT DO THIS
 * withContext(Dispatchers.Main) {
 *     try {
 *         // some code using a resource
 *     } finally {
 *         // THIS IS INCORRECT
 *         withContext(NonCancellable + Dispatchers.Default) {
 *             // cleanup code that should not be cancelled
 *         } // this line may throw a `CancellationException`!
 *     }
 * }
 * ```
 *
 * In this case, if the parent job is cancelled, [withContext] will throw a [CancellationException] as soon
 * as it tries to switch back from the [Dispatchers.Default] dispatcher back to the original one.
 * The reason for this is that [withContext] obeys the **prompt cancellation** principle,
 * which means that dispatching back from it to the original context will fail with a [CancellationException]
 * even if the block passed to [withContext] finished successfully,
 * overriding the original exception thrown by the `try` block, if any.
 *
 * To avoid this, you should use [NonCancellable] as the only element in the context of the `withContext` call,
 * and then inside the block, you can switch to any dispatcher you need:
 *
 * ```
 * withContext(Dispatchers.Main) {
 *     try {
 *         // some code using a resource
 *     } finally {
 *         withContext(NonCancellable) {
 *             withContext(Dispatchers.Default) {
 *                 // cleanup code that should not be cancelled
 *             }
 *         }
 *     }
 * }
 * ```
 *
 * #### Launching child coroutines
 *
 * Child coroutines should not be started in `withContext(NonCancellable)` blocks in resource cleanup handlers directly.
 *
 * ```
 * // DO NOT DO THIS
 * withContext(Dispatchers.Main) {
 *     try {
 *         // some code using a resource
 *     } finally {
 *         // THIS IS INCORRECT
 *         withContext(NonCancellable) {
 *             // cleanup code that should not be cancelled
 *             launch { delay(100.milliseconds) }
 *         } // this line may throw a `CancellationException`!
 *     }
 * }
 * ```
 *
 * Similarly to the case of specifying a dispatcher alongside [NonCancellable] in a [withContext] argument,
 * having to wait for child coroutines can lead to a dispatch at the end of the [withContext] call,
 * which will lead to it throwing a [CancellationException] due to the prompt cancellation guarantee.
 *
 * The solution to this is also similar:
 *
 * ```
 * withContext(Dispatchers.Main) {
 *     try {
 *         // some code using a resource
 *     } finally {
 *         withContext(NonCancellable) {
 *             // note: `coroutineScope` here is required
 *             // to prevent a sporadic CancellationException
 *             coroutineScope {
 *                 // cleanup code that should not be cancelled
 *                 launch { delay(100.milliseconds) }
 *             }
 *         }
 *     }
 * }
 * ```
 *
 * Because now [coroutineScope] and not [withContext] has to wait for the children, there is once again no dispatch
 * between the last line of the [withContext] block and getting back to the caller.
 *
 * ### Not reacting to cancellations right outside the [withContext]
 *
 * Just like combining [NonCancellable] with other elements is incorrect because cancellation may override
 * the original exception, the opposite can also be incorrect, depending on the context:
 *
 * ```
 * // DO NOT DO THIS
 * withContext(Dispatchers.Main) {
 *     withContext(NonCancellable) {
 *         withContext(Dispatchers.Default) {
 *             // do something
 *         }
 *     } // will not react to the caller's cancellation!
 *     // BUG HERE
 *     updateUi() // may be invoked when the caller is already cancelled
 * }
 * ```
 *
 * Here, the following may happen:
 * 1. The `do something` block gets entered, and the main thread gets released and is free to perform other tasks.
 * 2. Some other task updates the UI and cancels this coroutine, which is no longer needed.
 * 3. `do something` finishes, and the computation is dispatched back to the main thread.
 * 4. `updateUi()` is called, even though the coroutine was already cancelled and the UI is no longer in a valid state
 *    for this update operation, potentially leading to a crash.
 *
 * [ensureActive] can be used to manually ensure that cancelled code no longer runs:
 *
 * ```
 * withContext(Dispatchers.Main) {
 *     withContext(NonCancellable) {
 *         withContext(Dispatchers.Default) {
 *             // do something
 *         }
 *     }
 *     ensureActive() // check if we are still allowed to run the code
 *     updateUi()
 * }
 * ```
 *
 */
@OptIn(InternalForInheritanceCoroutinesApi::class)
public object NonCancellable : AbstractCoroutineContextElement(Job), Job {

    private const val message = "NonCancellable can be used only as an argument for 'withContext', direct usages of its API are prohibited"

    /**
     * Always returns `null`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val parent: Job?
        get() = null

    /**
     * Always returns `true`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val isActive: Boolean
        get() = true

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val isCompleted: Boolean get() = false

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val isCancelled: Boolean get() = false

    /**
     * Always returns `false`.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun start(): Boolean = false

    /**
     * Always throws [UnsupportedOperationException].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override suspend fun join() {
        throw UnsupportedOperationException("This job is always active")
    }

    /**
     * Always throws [UnsupportedOperationException].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val onJoin: SelectClause0
        get() = throw UnsupportedOperationException("This job is always active")

    /**
     * Always throws [IllegalStateException].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun getCancellationException(): CancellationException = throw IllegalStateException("This job is always active")

    /**
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /**
     * Always returns no-op handle.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun invokeOnCompletion(onCancelling: Boolean, invokeImmediately: Boolean, handler: CompletionHandler): DisposableHandle =
        NonDisposableHandle

    /**
     * Does nothing.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun cancel(cause: CancellationException?) {}

    /**
     * Always returns `false`.
     * @suppress This method has bad semantics when cause is not a [CancellationException]. Use [cancel].
     */
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    override fun cancel(cause: Throwable?): Boolean = false // never handles exceptions

    /**
     * Always returns [emptySequence].
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override val children: Sequence<Job>
        get() = emptySequence()

    /**
     * Always returns [NonDisposableHandle] and does not do anything.
     * @suppress **This an internal API and should not be used from general code.**
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = message)
    override fun attachChild(child: ChildJob): ChildHandle = NonDisposableHandle

    /** @suppress */
    override fun toString(): String {
        return "NonCancellable"
    }
}
