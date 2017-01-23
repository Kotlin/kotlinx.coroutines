package kotlinx.coroutines.experimental

import kotlin.coroutines.ContinuationInterceptor

/**
 * This dispatcher _feature_ is implemented by [CoroutineDispatcher] implementations that
 * natively support [yield] function.
 */
public interface Yield {
    /**
     * Yields a thread (or thread pool) of this dispatcher to other coroutines to run.
     * This suspending function is cancellable.
     * If the [Job] of the current coroutine is completed while this suspending function is suspended, this function
     * resumes with [CancellationException].
     */
    suspend fun yield(): Unit = suspendCancellableCoroutine { cont -> scheduleResume(cont) }

    /**
     * Schedules resume of a specified [continuation] in this dispatcher's thread (or pool of threads).
     */
    fun scheduleResume(continuation: CancellableContinuation<Unit>)
}

/**
 * Yields a thread (or thread pool) of the current coroutine dispatcher to other coroutines to run.
 * If the coroutine dispatcher does not have its own thread pool (like [Here] dispatcher) and does not implement
 * [Yield], then the [Yield] implementation is taken from the context, if there is none, then this
 * function does nothing, but checks if the coroutine [Job] was cancelled.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is completed while this suspending function is suspended, this function
 * resumes with [CancellationException].
 */
suspend fun yield(): Unit = suspendCancellableCoroutine sc@ { cont ->
    (cont.context[ContinuationInterceptor] as? Yield)?.apply {
        scheduleResume(cont)
        return@sc
    }
    cont.resume(Unit)
}
