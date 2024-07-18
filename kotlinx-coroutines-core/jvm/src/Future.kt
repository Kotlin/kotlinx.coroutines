@file:JvmMultifileClass
@file:JvmName("JobKt")

package kotlinx.coroutines

import java.util.concurrent.*

/**
 * Cancels a specified [future] when this job is cancelled.
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCancellation { if (it != null) future.cancel(false) }
 * ```
 */
// Warning since 1.9.0
@Deprecated(
    "This function does not do what its name implies: it will not cancel the future if just cancel() was called.",
    level = DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("this.invokeOnCancellation { future.cancel(false) }")
)
public fun CancellableContinuation<*>.cancelFutureOnCancellation(future: Future<*>): Unit =
    invokeOnCancellation(handler = PublicCancelFutureOnCancel(future))

private class PublicCancelFutureOnCancel(private val future: Future<*>) : CancelHandler {
    override fun invoke(cause: Throwable?) {
        // Don't interrupt when cancelling future on completion, because no one is going to reset this
        // interruption flag and it will cause spurious failures elsewhere
        if (cause != null)  future.cancel(false)
    }
    override fun toString() = "CancelFutureOnCancel[$future]"
}
