package kotlinx.coroutines.experimental

/**
 * Yields a thread (or thread pool) of the current coroutine dispatcher to other coroutines to run.
 * If the coroutine dispatcher does not have its own thread pool (like [Unconfined] dispatcher) then this
 * function does nothing, but checks if the coroutine [Job] was completed.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is completed when this suspending function is invoked or while
 * this function is waiting for dispatching, it resumes with [CancellationException].
 */
suspend fun yield(): Unit = suspendCancellableCoroutine sc@ { cont ->
    (cont as SafeCancellableContinuation).resumeYield(Unit)
}
