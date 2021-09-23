/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicInteger

/**
 * Creates a coroutine execution context using a single thread with built-in [yield] support.
 * **NOTE: The resulting [ExecutorCoroutineDispatcher] owns native resources (its thread).
 * Resources are reclaimed by [ExecutorCoroutineDispatcher.close].**
 *
 * If the resulting dispatcher is [closed][ExecutorCoroutineDispatcher.close] and
 * attempt to submit a continuation task is made,
 * then the [Job] of the affected task is [cancelled][Job.cancel] and the task is submitted to the
 * [Dispatchers.IO], so that the affected coroutine can cleanup its resources and promptly complete.
 *
 * This is a **delicate** API. The result of this method is a closeable resource with the
 * associated native resources (threads). It should not be allocated in place,
 * should be closed at the end of its lifecycle, and has non-trivial memory and CPU footprint.
 * If you do not need a separate thread-pool, but only have to limit effective parallelism of the dispatcher,
 * it is recommended to use [CoroutineDispatcher.limitedParallelism] instead.
 *
 * If you need a completely separate thread-pool with scheduling policy that is based on the standard
 * JDK executors, use the following expression:
 * `Executors.newSingleThreadExecutor().asCoroutineDispatcher()`.
 * See [Executor.asCoroutineDispatcher] for details.
 *
 * @param name the base name of the created thread.
 */
@DelicateCoroutinesApi
public fun newSingleThreadContext(name: String): ExecutorCoroutineDispatcher =
    newFixedThreadPoolContext(1, name)

/**
 * Creates a coroutine execution context with the fixed-size thread-pool and built-in [yield] support.
 * **NOTE: The resulting [ExecutorCoroutineDispatcher] owns native resources (its threads).
 * Resources are reclaimed by [ExecutorCoroutineDispatcher.close].**
 *
 * If the resulting dispatcher is [closed][ExecutorCoroutineDispatcher.close] and
 * attempt to submit a continuation task is made,
 * then the [Job] of the affected task is [cancelled][Job.cancel] and the task is submitted to the
 * [Dispatchers.IO], so that the affected coroutine can cleanup its resources and promptly complete.
 *
 * This is a **delicate** API. The result of this method is a closeable resource with the
 * associated native resources (threads). It should not be allocated in place,
 * should be closed at the end of its lifecycle, and has non-trivial memory and CPU footprint.
 * If you do not need a separate thread-pool, but only have to limit effective parallelism of the dispatcher,
 * it is recommended to use [CoroutineDispatcher.limitedParallelism] instead.
 *
 * If you need a completely separate thread-pool with scheduling policy that is based on the standard
 * JDK executors, use the following expression:
 * `Executors.newFixedThreadPool().asCoroutineDispatcher()`.
 * See [Executor.asCoroutineDispatcher] for details.
 *
 * @param nThreads the number of threads.
 * @param name the base name of the created threads.
 */
@DelicateCoroutinesApi
public fun newFixedThreadPoolContext(nThreads: Int, name: String): ExecutorCoroutineDispatcher {
    require(nThreads >= 1) { "Expected at least one thread, but $nThreads specified" }
    val threadNo = AtomicInteger()
    val executor = Executors.newScheduledThreadPool(nThreads) { runnable ->
        val t = Thread(runnable, if (nThreads == 1) name else name + "-" + threadNo.incrementAndGet())
        t.isDaemon = true
        t
    }
    return executor.asCoroutineDispatcher()
}
