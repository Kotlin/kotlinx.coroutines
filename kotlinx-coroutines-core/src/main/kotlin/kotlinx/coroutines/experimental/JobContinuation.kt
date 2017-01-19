package kotlinx.coroutines.experimental

import kotlin.coroutines.Continuation
import kotlin.coroutines.CoroutineContext

// internal helper class for various primitives that combines Job and Continuation implementations
@Suppress("LeakingThis")
internal open class JobContinuation<in T>(
    parentContext: CoroutineContext
) : JobSupport(parentContext[Job]), Continuation<T> {
    override val context: CoroutineContext = parentContext + this // mixes this job into this context

    override fun resume(value: T) {
        while (true) { // lock-free loop on state
            val state = getState() // atomic read
            when (state) {
                is Active -> if (updateState(state, value)) return
                is Cancelled -> return // ignore resumes on cancelled continuation
                else -> throw IllegalStateException("Already resumed, but got value $value")
            }
        }
    }

    override fun resumeWithException(exception: Throwable) {
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

    override fun afterCompletion(state: Any?, closeException: Throwable?) {
        if (closeException != null) handleCoroutineException(context, closeException)
    }
}
