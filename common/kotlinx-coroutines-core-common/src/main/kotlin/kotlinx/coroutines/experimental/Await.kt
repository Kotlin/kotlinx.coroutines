/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import kotlinx.atomicfu.atomic

/**
 * Awaits for completion of given deferred values without blocking a thread and resumes normally with the list of values
 * when all deferred computations are complete or resumes with the first thrown exception if any of computations
 * complete exceptionally including cancellation.
 *
 * This function is **not** equivalent to `deferreds.map { it.await() }` which fails only when when it sequentially
 * gets to wait the failing deferred, while this `awaitAll` fails immediately as soon as any of the deferreds fail.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
public suspend fun <T> awaitAll(vararg deferreds: Deferred<T>): List<T> =
    if (deferreds.isEmpty()) emptyList() else AwaitAll(deferreds).await()

/**
 * Awaits for completion of given deferred values without blocking a thread and resumes normally with the list of values
 * when all deferred computations are complete or resumes with the first thrown exception if any of computations
 * complete exceptionally including cancellation.
 *
 * This function is **not** equivalent to `this.map { it.await() }` which fails only when when it sequentially
 * gets to wait the failing deferred, while this `awaitAll` fails immediately as soon as any of the deferreds fail.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
public suspend fun <T> Collection<Deferred<T>>.awaitAll(): List<T> =
    if (isEmpty()) emptyList() else AwaitAll(toTypedArray()).await()

/**
 * Suspends current coroutine until all given jobs are complete.
 * This method is semantically equivalent to joining all given jobs one by one with `jobs.forEach { it.join() }`.
 *
 * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
public suspend fun joinAll(vararg jobs: Job): Unit = jobs.forEach { it.join() }

/**
 * Suspends current coroutine until all given jobs are complete.
 * This method is semantically equivalent to joining all given jobs one by one with `forEach { it.join() }`.
 *
 * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 */
public suspend fun Collection<Job>.joinAll(): Unit = forEach { it.join() }

private class AwaitAll<T>(private val deferreds: Array<out Deferred<T>>) {
    private val notCompletedCount = atomic(deferreds.size)

    suspend fun await(): List<T> = suspendCancellableCoroutine { cont ->
        val handlers = deferreds.map {
            it.start() // To properly await lazily started deferreds
            it.invokeOnCompletion(AwaitAllNode(cont, it).asHandler)
        }
        cont.invokeOnCancellation(handler = DisposeHandlersOnCancel(handlers).asHandler)
    }

    private class DisposeHandlersOnCancel(private val handlers: List<DisposableHandle>) : CancelHandler() {
        override fun invoke(cause: Throwable?) {
            handlers.forEach { it.dispose() }
        }
        override fun toString(): String = "DisposeHandlersOnCancel[$handlers]"
    }

    private inner class AwaitAllNode(private val continuation: CancellableContinuation<List<T>>, job: Job) : JobNode<Job>(job) {
        override fun invoke(cause: Throwable?) {
            if (cause != null) {
                val token = continuation.tryResumeWithException(cause)
                if (token != null) {
                    continuation.completeResume(token)
                }
            } else if (notCompletedCount.decrementAndGet() == 0) {
                continuation.resume(deferreds.map { it.getCompleted() })
            }
        }
    }
}
