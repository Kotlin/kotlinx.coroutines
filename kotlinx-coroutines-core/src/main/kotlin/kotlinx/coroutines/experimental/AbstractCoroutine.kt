package kotlinx.coroutines.experimental

import kotlin.coroutines.Continuation
import kotlin.coroutines.CoroutineContext

/**
 * Abstract class to simplify writing of coroutine completion objects that
 * implements [Continuation] and [Job] interfaces.
 * It stores the result of continuation in the state of the job.
 */
@Suppress("LeakingThis")
public abstract class AbstractCoroutine<in T>(parentContext: CoroutineContext) : JobSupport(), Continuation<T> {
    override val context: CoroutineContext = parentContext + this // merges this job into this context

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
