/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.*
import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.coroutines.experimental.*

/**
 * Creates a new coroutine execution context using a single thread with built-in [yield] support.
 * **NOTE: The resulting [ExecutorCoroutineDispatcher] owns native resources (its thread).
 * Resources are reclaimed by [ExecutorCoroutineDispatcher.close].**
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
fun newSingleThreadContext(name: String): ExecutorCoroutineDispatcher =
    newFixedThreadPoolContext(1, name)

/**
 * @suppress binary compatibility
 */
@JvmName("newSingleThreadContext")
@Deprecated(level = DeprecationLevel.HIDDEN, message = "Binary compatibility only")
fun newSingleThreadContext0(name: String): ThreadPoolDispatcher =
    newSingleThreadContext(name) as ThreadPoolDispatcher

/**
 * @suppress **Deprecated**: Parent job is no longer supported.
 */
@Deprecated(message = "Parent job is no longer supported, `close` the resulting ThreadPoolDispatcher to release resources",
    level = DeprecationLevel.WARNING, replaceWith = ReplaceWith("newSingleThreadContext(name)"))
fun newSingleThreadContext(name: String, parent: Job? = null): CoroutineContext =
    newFixedThreadPoolContext(1, name)

/**
 * Creates new coroutine execution context with the fixed-size thread-pool and built-in [yield] support.
 * **NOTE: The resulting [ExecutorCoroutineDispatcher] owns native resources (its threads).
 * Resources are reclaimed by [ExecutorCoroutineDispatcher.close].**
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
fun newFixedThreadPoolContext(nThreads: Int, name: String): ExecutorCoroutineDispatcher {
    require(nThreads >= 1) { "Expected at least one thread, but $nThreads specified" }
    return ThreadPoolDispatcher(nThreads, name)
}

/**
 * @suppress binary compatibility
 */
@JvmName("newFixedThreadPoolContext")
@Deprecated(level = DeprecationLevel.HIDDEN, message = "Binary compatibility only")
fun newFixedThreadPoolContext0(nThreads: Int, name: String): ThreadPoolDispatcher =
    newFixedThreadPoolContext(nThreads, name) as ThreadPoolDispatcher

/**
 * @suppress **Deprecated**: Parent job is no longer supported.
 */
@Deprecated(message = "Parent job is no longer supported, `close` the resulting ThreadPoolDispatcher to release resources",
    level = DeprecationLevel.WARNING, replaceWith = ReplaceWith("newFixedThreadPoolContext(nThreads, name)"))
fun newFixedThreadPoolContext(nThreads: Int, name: String, parent: Job? = null): CoroutineContext =
    newFixedThreadPoolContext(nThreads, name)

internal class PoolThread(
    @JvmField val dispatcher: ThreadPoolDispatcher, // for debugging & tests
    target: Runnable, name: String
) : Thread(target, name) {
    init { isDaemon = true }
}

/**
 * Dispatches coroutine execution to a thread pool of a fixed size. Instances of this dispatcher are
 * created with [newSingleThreadContext] and [newFixedThreadPoolContext].
 * 
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
@Deprecated("Replace with ExecutorCoroutineDispatcher", replaceWith = ReplaceWith("ExecutorCoroutineDispatcher"))
public class ThreadPoolDispatcher internal constructor(
    private val nThreads: Int,
    private val name: String
) : ExecutorCoroutineDispatcherBase() {
    private val threadNo = AtomicInteger()

    override val executor: Executor = Executors.newScheduledThreadPool(nThreads) { target ->
        PoolThread(this, target, if (nThreads == 1) name else name + "-" + threadNo.incrementAndGet())
    }

    init {
        initFutureCancellation()
    }

    /**
     * Closes this dispatcher -- shuts down all threads in this pool and releases resources.
     */
    public override fun close() {
        (executor as ExecutorService).shutdown()
    }

    override fun toString(): String = "ThreadPoolDispatcher[$nThreads, $name]"
}
