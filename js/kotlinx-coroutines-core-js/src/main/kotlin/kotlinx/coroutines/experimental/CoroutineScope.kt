package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.CoroutineContext

/**
 * Receiver interface for generic coroutine builders, so that the code inside coroutine has a convenient access
 * to its [coroutineContext] and its cancellation status via [isActive].
 */
public actual interface CoroutineScope {
    /**
     * Returns `true` when this coroutine is still active (has not completed and was not cancelled yet).
     *
     * Check this property in long-running computation loops to support cancellation:
     * ```
     * while (isActive) {
     *     // do some computation
     * }
     * ```
     *
     * This property is a shortcut for `coroutineContext[Job]!!.isActive`. See [coroutineContext] and [Job].
     */
    public actual val isActive: Boolean

    /**
     * Returns the context of this coroutine.
     */
    public actual val coroutineContext: CoroutineContext
}