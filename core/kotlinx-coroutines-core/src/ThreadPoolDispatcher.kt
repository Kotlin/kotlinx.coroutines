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

import java.io.Closeable
import java.util.concurrent.Executors
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.atomic.AtomicInteger
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Creates a new coroutine execution context using a single thread with built-in [yield] and [delay] support.
 * **NOTE: The resulting [ThreadPoolDispatcher] owns native resources (its thread).
 * Resources are reclaimed by [ThreadPoolDispatcher.close].**
 *
 * @param name the base name of the created thread.
 */
fun newSingleThreadContext(name: String): ThreadPoolDispatcher =
    newFixedThreadPoolContext(1, name)

/**
 * @suppress **Deprecated**: Parent job is no longer supported.
 */
@Deprecated(message = "Parent job is no longer supported, `close` the resulting ThreadPoolDispatcher to release resources",
    level = DeprecationLevel.WARNING, replaceWith = ReplaceWith("newSingleThreadContext(name)"))
fun newSingleThreadContext(name: String, parent: Job? = null): CoroutineContext =
    newFixedThreadPoolContext(1, name)

/**
 * Creates new coroutine execution context with the fixed-size thread-pool and built-in [yield] and [delay] support.
 * **NOTE: The resulting [ThreadPoolDispatcher] owns native resources (its threads).
 * Resources are reclaimed by [ThreadPoolDispatcher.close].**
 *
 * @param nThreads the number of threads.
 * @param name the base name of the created threads.
 */
fun newFixedThreadPoolContext(nThreads: Int, name: String): ThreadPoolDispatcher {
    require(nThreads >= 1) { "Expected at least one thread, but $nThreads specified" }
    return ThreadPoolDispatcher(nThreads, name)
}

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
 */
public class ThreadPoolDispatcher internal constructor(
    private val nThreads: Int,
    private val name: String
) : ExecutorCoroutineDispatcherBase(), Closeable {
    private val threadNo = AtomicInteger()

    internal override val executor: ScheduledExecutorService = Executors.newScheduledThreadPool(nThreads) { target ->
        PoolThread(this, target, if (nThreads == 1) name else name + "-" + threadNo.incrementAndGet())
    }

    /**
     * Closes this dispatcher -- shuts down all threads in this pool and releases resources.
     */
    public override fun close() {
        executor.shutdown()
    }

    override fun toString(): String = "ThreadPoolDispatcher[$nThreads, $name]"
}
