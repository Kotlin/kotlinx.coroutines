/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.exceptions.*
import kotlin.coroutines.*
import kotlin.test.*

class LimitedParallelismConcurrentTest : TestBase() {

    private val targetParallelism = 4
    private val iterations = 100_000
    private val parallelism = atomic(0)

    private fun checkParallelism() {
        val value = parallelism.incrementAndGet()
        randomWait()
        assertTrue { value <= targetParallelism }
        parallelism.decrementAndGet()
    }

    @Test
    fun testLimitedExecutor() = runTest {
        val executor = newFixedThreadPoolContext(targetParallelism, "test")
        val view = executor.limitedParallelism(targetParallelism)
        doStress {
            repeat(iterations) {
                launch(view) {
                    checkParallelism()
                }
            }
        }
        executor.close()
    }

    private suspend inline fun doStress(crossinline block: suspend CoroutineScope.() -> Unit) {
        repeat(stressTestMultiplier) {
            coroutineScope {
                block()
            }
        }
    }

    @Test
    fun testTaskFairness() = runTest {
        val executor = newSingleThreadContext("test")
        val view = executor.limitedParallelism(1)
        val view2 = executor.limitedParallelism(1)
        val j1 = launch(view) {
            while (true) {
                yield()
            }
        }
        val j2 = launch(view2) { j1.cancel() }
        joinAll(j1, j2)
        executor.close()
    }

    /**
     * Tests that, when no tasks are present, the limited dispatcher does not dispatch any tasks.
     * This is important for the case when a dispatcher is closeable and the [CoroutineDispatcher.limitedParallelism]
     * machinery could trigger a dispatch after the dispatcher is closed.
     */
    @Test
    fun testNotDoingDispatchesWhenNoTasksArePresent() = runTest {
        class NaggingDispatcher: CoroutineDispatcher() {
            val closed = atomic(false)
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                if (closed.value)
                    fail("Dispatcher was closed, but still dispatched a task")
                Dispatchers.Default.dispatch(context, block)
            }
            fun close() {
                closed.value = true
            }
        }
        repeat(stressTestMultiplier * 500_000) {
            val dispatcher = NaggingDispatcher()
            val view = dispatcher.limitedParallelism(1)
            val deferred = CompletableDeferred<Unit>()
            val job = launch(view) {
                deferred.await()
            }
            launch(Dispatchers.Default) {
                deferred.complete(Unit)
            }
            job.join()
            dispatcher.close()
        }
    }
}
