package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.NonCancellable.isActive
import kotlin.coroutines.AbstractCoroutineContextElement

/**
 * A non-cancelable job that is always [active][isActive]. It is designed to be used with [run] builder
 * to prevent cancellation of code blocks that need to run without cancellation, like this
 * ```
 * run(NonCancellable) {
 *     // this code will not be cancelled
 * }
 * ```
 */
object NonCancellable : AbstractCoroutineContextElement(Job), Job {
    override val isActive: Boolean  get() = true
    override fun getInactiveCancellationException(): CancellationException = throw IllegalStateException("This job is always active")
    override fun onCompletion(handler: CompletionHandler): Job.Registration = EmptyRegistration
    override fun cancel(reason: Throwable?): Boolean = false
}
