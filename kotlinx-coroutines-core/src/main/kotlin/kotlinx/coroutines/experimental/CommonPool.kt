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

import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicInteger
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Represents common pool of shared threads as coroutine dispatcher for compute-intensive tasks.
 * It uses [java.util.concurrent.ForkJoinPool] when available, which implements efficient work-stealing algorithm for its queues, so every
 * coroutine resumption is dispatched as a separate task even when it already executes inside the pool.
 * When available, it wraps `ForkJoinPool.commonPool` and provides a similar shared pool where not.
 */
object CommonPool : CoroutineDispatcher() {
    private val pool: ExecutorService = findPool()

    private inline fun <T> Try(block: () -> T) = try { block() } catch (e: Throwable) { null }

    private fun findPool(): ExecutorService {
        val fjpClass = Try { Class.forName("java.util.concurrent.ForkJoinPool") }
            ?: return createPlainPool()
        Try { fjpClass.getMethod("commonPool")?.invoke(null) as? ExecutorService }
            ?. let { return it }
        Try { fjpClass.getConstructor(Int::class.java).newInstance(defaultParallelism()) as? ExecutorService }
            ?. let { return it }
        return createPlainPool()
    }

    private fun createPlainPool(): ExecutorService {
        val threadId = AtomicInteger()
        return Executors.newFixedThreadPool(defaultParallelism()) {
            Thread(it, "CommonPool-worker-${threadId.incrementAndGet()}").apply { isDaemon = true }
        }
    }

    private fun defaultParallelism() = (Runtime.getRuntime().availableProcessors() - 1).coerceAtLeast(1)

    override fun dispatch(context: CoroutineContext, block: Runnable) = pool.execute(block)
}
