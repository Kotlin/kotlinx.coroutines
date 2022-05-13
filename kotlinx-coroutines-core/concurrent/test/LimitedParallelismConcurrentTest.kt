/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.exceptions.*
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
    fun testLimitedExecutor() = runMtTest {
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
    fun testTaskFairness() = runMtTest {
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
}
