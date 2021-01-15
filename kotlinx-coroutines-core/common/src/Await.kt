/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlin.coroutines.*

/**
 * Awaits for completion of given deferred values without blocking a thread and resumes normally with the list of values
 * when all deferred computations are complete or resumes with the first thrown exception if any of computations
 * complete exceptionally including cancellation.
 *
 * This function is **not** equivalent to `deferreds.map { it.await() }` which fails only when it sequentially
 * gets to wait for the failing deferred, while this `awaitAll` fails immediately as soon as any of the deferreds fail.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
 * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
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
 * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
 * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
 */
public suspend fun <T> Collection<Deferred<T>>.awaitAll(): List<T> =
    if (isEmpty()) emptyList() else AwaitAll(toTypedArray()).await()

/**
 * Suspends current coroutine until all given jobs are complete.
 * This method is semantically equivalent to joining all given jobs one by one with `jobs.forEach { it.join() }`.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
 * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
 */
public suspend fun joinAll(vararg jobs: Job): Unit = jobs.forEach { it.join() }

/**
 * Suspends current coroutine until all given jobs are complete.
 * This method is semantically equivalent to joining all given jobs one by one with `forEach { it.join() }`.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting,
 * this function immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
 * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
 */
public suspend fun Collection<Job>.joinAll(): Unit = forEach { it.join() }

private class AwaitAll<T>(private val deferreds: Array<out Deferred<T>>) {
    private val notCompletedCount = atomic(deferreds.size)

    suspend fun await(): List<T> = suspendCancellableCoroutine { cont ->
        // Intricate dance here
        // Step 1: Create nodes and install them as completion handlers, they may fire!
        val nodes = Array(deferreds.size) { i ->
            val deferred = deferreds[i]
            deferred.start() // To properly await lazily started deferreds
            AwaitAllNode(cont).apply {
                handle = deferred.invokeOnCompletion(asHandler)
            }
        }
        val disposer = DisposeHandlersOnCancel(nodes)
        // Step 2: Set disposer to each node
        nodes.forEach { it.disposer = disposer }
        // Here we know that if any code the nodes complete, it will dispose the rest
        // Step 3: Now we can check if continuation is complete
        if (cont.isCompleted) {
            // it is already complete while handlers were being installed -- dispose them all
            disposer.disposeAll()
        } else {
            cont.invokeOnCancellation(handler = disposer.asHandler)
        }
    }

    private inner class DisposeHandlersOnCancel(private val nodes: Array<AwaitAllNode>) : CancelHandler() {
        fun disposeAll() {
            nodes.forEach { it.handle.dispose() }
        }

        override fun invoke(cause: Throwable?) { disposeAll() }
        override fun toString(): String = "DisposeHandlersOnCancel[$nodes]"
    }

    private inner class AwaitAllNode(private val continuation: CancellableContinuation<List<T>>) : JobNode() {
        lateinit var handle: DisposableHandle

        private val _disposer = atomic<DisposeHandlersOnCancel?>(null)
        var disposer: DisposeHandlersOnCancel?
            get() = _disposer.value
            set(value) { _disposer.value = value }
        
        override fun invoke(cause: Throwable?) {
            if (cause != null) {
                val token = continuation.tryResumeWithException(cause)
                if (token != null) {
                    continuation.completeResume(token)
                    // volatile read of disposer AFTER continuation is complete
                    // and if disposer was already set (all handlers where already installed, then dispose them all)
                    disposer?.disposeAll()
                }
            } else if (notCompletedCount.decrementAndGet() == 0) {
                continuation.resume(deferreds.map { it.getCompleted() })
                // Note that all deferreds are complete here, so we don't need to dispose their nodes
            }
        }
    }
}
