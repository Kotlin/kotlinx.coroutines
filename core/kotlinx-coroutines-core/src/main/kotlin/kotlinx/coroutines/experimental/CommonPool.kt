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

import kotlinx.coroutines.experimental.timeunit.TimeUnit
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.experimental.*

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
object CommonPool : CoroutineDispatcher() {

    /**
     * Name of the property that controls default parallelism level of [CommonPool].
     * If the property is not specified, `Runtime.getRuntime().availableProcessors() - 1` will be used instead (or `1` for single-core JVM).
     * Note that until Java 10, if an application is run within a container,
     * `Runtime.getRuntime().availableProcessors()` is not aware of container constraints and will return the real number of cores.
     */
    public const val DEFAULT_PARALLELISM_PROPERTY_NAME = "kotlinx.coroutines.default.parallelism"

    private val parallelism = run<Int> {
        val property = Try { System.getProperty(DEFAULT_PARALLELISM_PROPERTY_NAME) }
        if (property == null) {
            (Runtime.getRuntime().availableProcessors() - 1).coerceAtLeast(1)
        } else {
            val parallelism = property.toIntOrNull()
            if (parallelism == null || parallelism < 1) {
                error("Expected positive number in $DEFAULT_PARALLELISM_PROPERTY_NAME, but has $property")
            }
            parallelism
        }
    }

    // For debug and tests
    private var usePrivatePool = false

    @Volatile
    private var pool: Executor? = null

    private inline fun <T> Try(block: () -> T) = try { block() } catch (e: Throwable) { null }

    private fun createPool(): ExecutorService {
        if (System.getSecurityManager() != null) return createPlainPool()
        val fjpClass = Try { Class.forName("java.util.concurrent.ForkJoinPool") }
            ?: return createPlainPool()
        if (!usePrivatePool) {
            Try { fjpClass.getMethod("commonPool")?.invoke(null) as? ExecutorService }
                ?.let { return it }
        }
        Try { fjpClass.getConstructor(Int::class.java).newInstance(parallelism) as? ExecutorService }
            ?. let { return it }
        return createPlainPool()
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

    override fun dispatch(context: CoroutineContext, block: Runnable) =
        try { (pool ?: getOrCreatePoolSync()).execute(timeSource.trackTask(block)) }
        catch (e: RejectedExecutionException) {
            timeSource.unTrackTask()
            DefaultExecutor.execute(block)
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
            shutdownNow().forEach { DefaultExecutor.execute(it) }
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
}
