package kotlinx.coroutines.experimental

import kotlinx.atomicfu.atomic

/**
 * Awaits for completion of given jobs without blocking a thread and resumes normally when all deferred computations are complete
 * or resumes with the first thrown exception if any of computations completes exceptionally including cancellation.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
suspend fun awaitAll(vararg jobs: Job): Unit = jobs.asList().awaitAll()

/**
 * Awaits for completion of given jobs without blocking a thread and resumes normally when all jobs computations are complete
 * or resumes with the first thrown exception if any of computations completes exceptionally including cancellation.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is l or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
suspend fun Iterable<Job>.awaitAll(): Unit {
    val jobs = this as? Collection<Job> ?: this.toList()
    if (jobs.isEmpty()) {
        return
    }

    AwaitAll(jobs).await()
}

/**
 * Suspends current coroutine until all given jobs are complete. This method is semantically equivalent to joining all given jobs one by one.
 * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
suspend fun joinAll(vararg jobs: Job): Unit = jobs.forEach { it.join() }

/**
 * Suspends current coroutine until all given jobs are complete. This method is semantically equivalent to
 * joining all given jobs one by one.
 * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
suspend fun Iterable<Job>.joinAll(): Unit = forEach { it.join() }

private class AwaitAll(private val jobs: Collection<Job>) {
    private val notCompletedCount = atomic(jobs.size)

    suspend fun await() {
        suspendCancellableCoroutine<Unit> { cont ->
            val handler: (Throwable?) -> Unit = {
                if (it != null) {
                    val token = cont.tryResumeWithException(it)
                    if (token != null) {
                        cont.completeResume(token)
                    }
                } else if (notCompletedCount.decrementAndGet() == 0) {
                    cont.resume(Unit)
                }
            }

            jobs.forEach {
                cont.disposeOnCompletion(it.invokeOnCompletion(handler))
            }
        }
    }
}
