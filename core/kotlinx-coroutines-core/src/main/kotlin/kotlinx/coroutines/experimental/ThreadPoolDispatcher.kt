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

import java.util.concurrent.Executors
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.atomic.AtomicInteger
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Creates new coroutine execution context with the a single thread and built-in [yield] and [delay] support.
 * All continuations are dispatched immediately when invoked inside the thread of this context.
 * Resources of this pool (its thread) are reclaimed when job of this context is cancelled.
 * The specified [name] defines the name of the new thread.
 * An optional [parent] job may be specified upon creation.
 */
fun newSingleThreadContext(name: String, parent: Job? = null): CoroutineContext =
    newFixedThreadPoolContext(1, name, parent)

/**
 * Creates new coroutine execution context with the fixed-size thread-pool and built-in [yield] and [delay] support.
 * All continuations are dispatched immediately when invoked inside the threads of this context.
 * Resources of this pool (its threads) are reclaimed when job of this context is cancelled.
 * The specified [name] defines the names of the threads.
 * An optional [parent] job may be specified upon creation.
 */
fun newFixedThreadPoolContext(nThreads: Int, name: String, parent: Job? = null): CoroutineContext {
    require(nThreads >= 1) { "Expected at least one thread, but $nThreads specified" }
    val job = Job(parent)
    return job + ThreadPoolDispatcher(nThreads, name, job)
}

internal class PoolThread(
    @JvmField val dispatcher: ThreadPoolDispatcher, // for debugging & tests
    target: Runnable, name: String
) : Thread(target, name) {
    init { isDaemon = true }
}

internal class ThreadPoolDispatcher(
    private val nThreads: Int,
    private val name: String,
    job: Job
) : ExecutorCoroutineDispatcherBase() {
    private val threadNo = AtomicInteger()

    override val executor: ScheduledExecutorService = Executors.newScheduledThreadPool(nThreads) { target ->
        PoolThread(this, target, if (nThreads == 1) name else name + "-" + threadNo.incrementAndGet())
    }

    init {
        job.invokeOnCompletion { executor.shutdown() }
    }

    override fun toString(): String = "ThreadPoolDispatcher[$nThreads, $name]"
}
