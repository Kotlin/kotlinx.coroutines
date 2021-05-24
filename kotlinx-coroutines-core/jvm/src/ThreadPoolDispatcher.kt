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
 * **NOTE: This API will be replaced in the future**. A different API to create thread-limited thread pools
 * that is based on a shared thread-pool and does not require the resulting dispatcher to be explicitly closed
 * will be provided, thus avoiding potential thread leaks and also significantly improving performance, due
 * to coroutine-oriented scheduling policy and thread-switch minimization.
 * See [issue #261](https://github.com/Kotlin/kotlinx.coroutines/issues/261) for details.
 * If you need a completely separate thread-pool with scheduling policy that is based on the standard
 * JDK executors, use the following expression:
 * `Executors.newSingleThreadExecutor().asCoroutineDispatcher()`.
 * See [Executor.asCoroutineDispatcher] for details.
 *
 * @param name the base name of the created thread.
 */
@ObsoleteCoroutinesApi
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
 * **NOTE: This API will be replaced in the future**. A different API to create thread-limited thread pools
 * that is based on a shared thread-pool and does not require the resulting dispatcher to be explicitly closed
 * will be provided, thus avoiding potential thread leaks and also significantly improving performance, due
 * to coroutine-oriented scheduling policy and thread-switch minimization.
 * See [issue #261](https://github.com/Kotlin/kotlinx.coroutines/issues/261) for details.
 * If you need a completely separate thread-pool with scheduling policy that is based on the standard
 * JDK executors, use the following expression:
 * `Executors.newFixedThreadPool().asCoroutineDispatcher()`.
 * See [Executor.asCoroutineDispatcher] for details.
 *
 * @param nThreads the number of threads.
 * @param name the base name of the created threads.
 */
@ObsoleteCoroutinesApi
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
