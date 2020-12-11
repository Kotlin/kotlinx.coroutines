/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.*

/**
 * Represents common pool of shared threads as coroutine dispatcher for compute-intensive tasks.
 *
 * If there isn't a SecurityManager present it uses [java.util.concurrent.ForkJoinPool] when available, which implements
 * efficient work-stealing algorithm for its queues, so every coroutine resumption is dispatched as a separate task even
 * when it already executes inside the pool. When available, it wraps `ForkJoinPool.commonPool` and provides a similar
 * shared pool where not.
 * 
 * If there is a SecurityManager present (as would be if running inside a Java Web Start context) then a plain thread
 * pool is created. This is to work around the fact that ForkJoinPool creates threads that cannot perform
 * privileged actions.
 */
internal object CommonPool : ExecutorCoroutineDispatcher() {

    /**
     * Name of the property that controls default parallelism level of [CommonPool].
     * If the property is not specified, `Runtime.getRuntime().availableProcessors() - 1` will be used instead (or `1` for single-core JVM).
     * Note that until Java 10, if an application is run within a container,
     * `Runtime.getRuntime().availableProcessors()` is not aware of container constraints and will return the real number of cores.
     */
    private const val DEFAULT_PARALLELISM_PROPERTY_NAME = "kotlinx.coroutines.default.parallelism"

    override val executor: Executor
        get() = pool ?: getOrCreatePoolSync()

    // Equals to -1 if not explicitly specified
    private val requestedParallelism = run<Int> {
        val property = Try { System.getProperty(DEFAULT_PARALLELISM_PROPERTY_NAME) } ?: return@run -1
        val parallelism = property.toIntOrNull()
        if (parallelism == null || parallelism < 1) {
            error("Expected positive number in $DEFAULT_PARALLELISM_PROPERTY_NAME, but has $property")
        }
        parallelism
    }

    private val parallelism: Int
        get() = requestedParallelism.takeIf { it > 0 }
            ?: (Runtime.getRuntime().availableProcessors() - 1).coerceAtLeast(1)

    // For debug and tests
    private var usePrivatePool = false

    @Volatile
    private var pool: Executor? = null

    private inline fun <T> Try(block: () -> T) = try { block() } catch (e: Throwable) { null }

    private fun createPool(): ExecutorService {
        if (System.getSecurityManager() != null) return createPlainPool()
        // Reflection on ForkJoinPool class so that it works on JDK 6 (which is absent there)
        val fjpClass = Try { Class.forName("java.util.concurrent.ForkJoinPool") }
            ?: return createPlainPool() // Fallback to plain thread pool
        // Try to use commonPool unless parallelism was explicitly specified or in debug privatePool mode
        if (!usePrivatePool && requestedParallelism < 0) {
            Try { fjpClass.getMethod("commonPool").invoke(null) as? ExecutorService }
                ?.takeIf { isGoodCommonPool(fjpClass, it) }
                ?.let { return it }
        }
        // Try to create private ForkJoinPool instance
        Try { fjpClass.getConstructor(Int::class.java).newInstance(parallelism) as? ExecutorService }
            ?. let { return it }
        // Fallback to plain thread pool
        return createPlainPool()
    }

    /**
     * Checks that this ForkJoinPool's parallelism is at least one to avoid pathological bugs.
     */
    internal fun isGoodCommonPool(fjpClass: Class<*>, executor: ExecutorService): Boolean {
        // We cannot use getParallelism, since it lies to us (always returns at least 1)
        // So we submit a task and check that getPoolSize is at least one after that
        // A broken FJP (that is configured for 0 parallelism) would not execute the task and
        // would report its pool size as zero.
        executor.submit {}
        val actual = Try { fjpClass.getMethod("getPoolSize").invoke(executor) as? Int }
            ?: return false
        return actual >= 1
    }

    private fun createPlainPool(): ExecutorService {
        val threadId = AtomicInteger()
        return Executors.newFixedThreadPool(parallelism) {
            Thread(it, "CommonPool-worker-${threadId.incrementAndGet()}").apply { isDaemon = true }
        }
    }

    @Synchronized
    private fun getOrCreatePoolSync(): Executor =
        pool ?: createPool().also { pool = it }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        try {
            (pool ?: getOrCreatePoolSync()).execute(wrapTask(block))
        } catch (e: RejectedExecutionException) {
            unTrackTask()
            // CommonPool only rejects execution when it is being closed and this behavior is reserved
            // for testing purposes, so we don't have to worry about cancelling the affected Job here.
            DefaultExecutor.enqueue(block)
        }
    }

    // used for tests
    @Synchronized
    internal fun usePrivatePool() {
        shutdown(0)
        usePrivatePool = true
        pool = null
    }

    // used for tests
    @Synchronized
    internal fun shutdown(timeout: Long) {
        (pool as? ExecutorService)?.apply {
            shutdown()
            if (timeout > 0)
                awaitTermination(timeout, TimeUnit.MILLISECONDS)
            shutdownNow().forEach { DefaultExecutor.enqueue(it) }
        }
        pool = Executor { throw RejectedExecutionException("CommonPool was shutdown") }
    }

    // used for tests
    @Synchronized
    internal fun restore() {
        shutdown(0)
        usePrivatePool = false
        pool = null
    }

    override fun toString(): String = "CommonPool"

    override fun close(): Unit = error("Close cannot be invoked on CommonPool")
}
