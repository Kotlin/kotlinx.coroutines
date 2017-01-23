package kotlinx.coroutines.experimental

import kotlin.coroutines.AbstractCoroutineContextElement
import kotlin.coroutines.Continuation
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext

/**
 * Base class that shall be extended by all coroutine dispatcher implementations.
 *
 * The following standard implementations are provided by `kotlinx.coroutines`:
 * * [Here] -- starts coroutine execution _right here_ in the current call-frame until the first suspension. On first
 *   suspension the coroutine builder function returns. The coroutine will resume in whatever thread that is used by the
 *   corresponding suspending function, without mandating any specific threading policy.
 *   This in an appropriate choice for IO-intensive coroutines that do not consume CPU resources.
 * * [CommonPool] -- immediately returns from the coroutine builder and schedules coroutine execution to
 *   a common pool of shared background threads.
 *   This is an appropriate choice for compute-intensive coroutines that consume a lot of CPU resources.
 * * Private thread pools can be created with [newSingleThreadContext] and [newFixedThreadPoolContext].
 * * [currentCoroutineContext] -- inherits the context of the parent coroutine,
 *   but throws [IllegalStateException] if used outside of coroutine. Use [currentCoroutineContextOrDefault]
 *   if a default is needed when outside of coroutine.
 *   This is an appropriate choice for libraries that need to inherit parent coroutine context.
 * * There are context implementations for UI libraries like `Swing` and `JavaFx` in separate modules.
 *
 * This class ensures that [currentCoroutineContext] is correctly transferred to a new thread and that
 * debugging facilities in [newCoroutineContext] function work properly.
 */
public abstract class CoroutineDispatcher :
        AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {
    /**
     * Return `true` if execution shall be dispatched onto another thread.
     */
    public abstract fun isDispatchNeeded(context: CoroutineContext): Boolean

    /**
     * Dispatches execution of a runnable [block] onto another thread in the given [context].
     */
    public abstract fun dispatch(context: CoroutineContext, block: Runnable)

    override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> =
            DispatchedContinuation<T>(this, continuation)
}

private class DispatchedContinuation<T>(
        val dispatcher: CoroutineDispatcher,
        val continuation: Continuation<T>
): Continuation<T> by continuation {
    override fun resume(value: T) {
        val context = continuation.context
        if (dispatcher.isDispatchNeeded(context))
            dispatcher.dispatch(context, Runnable {
                withDefaultCoroutineContext(context) {
                    continuation.resume(value)
                }
            })
        else
            withDefaultCoroutineContext(context) {
                continuation.resume(value)
            }
    }

    override fun resumeWithException(exception: Throwable) {
        val context = continuation.context
        if (dispatcher.isDispatchNeeded(context))
            dispatcher.dispatch(context, Runnable {
                withDefaultCoroutineContext(context) {
                    continuation.resumeWithException(exception)
                }
            })
        else
            withDefaultCoroutineContext(context) {
                continuation.resumeWithException(exception)
            }
    }
}
