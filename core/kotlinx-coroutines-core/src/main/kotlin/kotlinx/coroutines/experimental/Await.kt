package kotlinx.coroutines.experimental

import kotlinx.atomicfu.atomic

/**
 * Awaits for completion of given jobs without blocking a thread and resumes normally when all deferred computations are complete
 * or resumes with the first thrown exception if any of computations completes exceptionally including cancellation.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
public suspend fun awaitAll(vararg jobs: Job): Unit = jobs.asList().awaitAll()

/**
 * Awaits for completion of given jobs without blocking a thread and resumes normally when all jobs computations are complete
 * or resumes with the first thrown exception if any of computations completes exceptionally including cancellation.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
public suspend fun Collection<Job>.awaitAll() {
    if (isEmpty()) return
    val snapshot = ArrayList(this)
    AwaitAll(snapshot).await()
}

/**
 * Suspends current coroutine until all given jobs are complete. This method is semantically equivalent to joining all given jobs one by one.
 * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
public suspend fun joinAll(vararg jobs: Job): Unit = jobs.forEach { it.join() }

/**
 * Suspends current coroutine until all given jobs are complete. This method is semantically equivalent to
 * joining all given jobs one by one.
 * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
public suspend fun Collection<Job>.joinAll(): Unit = forEach { it.join() }

private class AwaitAll(private val jobs: Collection<Job>) {
    private val notCompletedCount = atomic(jobs.size)

    suspend fun await() {
        suspendCancellableCoroutine<Unit> { cont ->
            jobs.forEach {
                it.start() // To properly await lazily started jobs
                cont.disposeOnCompletion(it.invokeOnCompletion(AwaitAllNode(cont, it)))
            }
        }
    }

    inner class AwaitAllNode(private val continuation: CancellableContinuation<Unit>, job: Job) : JobNode<Job>(job), CompletionHandler {

        override fun invoke(cause: Throwable?) {
            if (cause != null) {
                val token = continuation.tryResumeWithException(cause)
                if (token != null) {
                    continuation.completeResume(token)
                }
            } else if (notCompletedCount.decrementAndGet() == 0) {
                continuation.resume(Unit)
            }
        }
    }
}
