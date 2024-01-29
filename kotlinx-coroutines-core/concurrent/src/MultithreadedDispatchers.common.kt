@file:JvmMultifileClass
@file:JvmName("ThreadPoolDispatcherKt")
package kotlinx.coroutines

import kotlin.jvm.*

/**
 * Creates a coroutine execution context using a single thread with built-in [yield] support.
 * **NOTE: The resulting [CloseableCoroutineDispatcher] owns native resources (its thread).
 * Resources are reclaimed by [CloseableCoroutineDispatcher.close].**
 *
 * If the resulting dispatcher is [closed][CloseableCoroutineDispatcher.close] and
 * attempt to submit a task is made, then:
 * - On the JVM, the [Job] of the affected task is [cancelled][Job.cancel] and the task is submitted to the
 *   [Dispatchers.IO], so that the affected coroutine can clean up its resources and promptly complete.
 * - On Native, the attempt to submit a task throws an exception.
 *
 * This is a **delicate** API. The result of this method is a closeable resource with the
 * associated native resources (threads or native workers). It should not be allocated in place,
 * should be closed at the end of its lifecycle, and has non-trivial memory and CPU footprint.
 * If you do not need a separate thread pool, but only have to limit effective parallelism of the dispatcher,
 * it is recommended to use [CoroutineDispatcher.limitedParallelism] instead.
 *
 * If you need a completely separate thread pool with scheduling policy that is based on the standard
 * JDK executors, use the following expression:
 * `Executors.newSingleThreadExecutor().asCoroutineDispatcher()`.
 * See `Executor.asCoroutineDispatcher` for details.
 *
 * @param name the base name of the created thread.
 */
@ExperimentalCoroutinesApi
@DelicateCoroutinesApi
public fun newSingleThreadContext(name: String): CloseableCoroutineDispatcher =
    newFixedThreadPoolContext(1, name)

/**
 * Creates a coroutine execution context with the fixed-size thread-pool and built-in [yield] support.
 * **NOTE: The resulting [CoroutineDispatcher] owns native resources (its threads).
 * Resources are reclaimed by [CloseableCoroutineDispatcher.close].**
 *
 * If the resulting dispatcher is [closed][CloseableCoroutineDispatcher.close] and
 * attempt to submit a continuation task is made,
 * - On the JVM, the [Job] of the affected task is [cancelled][Job.cancel] and the task is submitted to the
 *   [Dispatchers.IO], so that the affected coroutine can clean up its resources and promptly complete.
 * - On Native, the attempt to submit a task throws an exception.
 *
 * This is a **delicate** API. The result of this method is a closeable resource with the
 * associated native resources (threads or native workers). It should not be allocated in place,
 * should be closed at the end of its lifecycle, and has non-trivial memory and CPU footprint.
 * If you do not need a separate thread pool, but only have to limit effective parallelism of the dispatcher,
 * it is recommended to use [CoroutineDispatcher.limitedParallelism] instead.
 *
 * If you need a completely separate thread pool with scheduling policy that is based on the standard
 * JDK executors, use the following expression:
 * `Executors.newFixedThreadPool().asCoroutineDispatcher()`.
 * See `Executor.asCoroutineDispatcher` for details.
 *
 * @param nThreads the number of threads.
 * @param name the base name of the created threads.
 */
@ExperimentalCoroutinesApi
public expect fun newFixedThreadPoolContext(nThreads: Int, name: String): CloseableCoroutineDispatcher
