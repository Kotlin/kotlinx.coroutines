package kotlinx.coroutines.experimental

import kotlin.coroutines.Continuation
import kotlin.coroutines.CoroutineContext

/**
 * Receiver interface for generic coroutine builders, so that the code inside coroutine has a convenient access
 * to its [context] and cancellation status via [isActive].
 */
public interface CoroutineScope {
    /**
     * Returns `true` when this coroutine is still active (was not cancelled).
     */
    public val isActive: Boolean

    /**
     * Returns the context of this coroutine.
     */
    public val context: CoroutineContext
}

/**
 * Abstract class to simplify writing of coroutine completion objects that
 * implements [Continuation] and [Job] interfaces.
 * It stores the result of continuation in the state of the job.
 */
@Suppress("LeakingThis")
public abstract class AbstractCoroutine<in T>(newContext: CoroutineContext) : JobSupport(), Continuation<T>, CoroutineScope {
    override val context: CoroutineContext = newContext + this // merges this job into this context

    final override fun resume(value: T) {
        while (true) { // lock-free loop on state
            val state = getState() // atomic read
            when (state) {
                is Active -> if (updateState(state, value)) return
                is Cancelled -> return // ignore resumes on cancelled continuation
                else -> throw IllegalStateException("Already resumed, but got value $value")
            }
        }
    }

    final override fun resumeWithException(exception: Throwable) {
        while (true) { // lock-free loop on state
            val state = getState() // atomic read
            when (state) {
                is Active -> if (updateState(state, Failed(exception))) return
                is Cancelled -> {
                    // ignore resumes on cancelled continuation, but handle exception if a different one is here
                    if (exception != state.exception) handleCoroutineException(context, exception)
                    return
                }
                else -> throw IllegalStateException("Already resumed, but got exception $exception", exception)
            }
        }
    }

    final override fun handleCompletionException(closeException: Throwable) {
        handleCoroutineException(context, closeException)
    }
}
