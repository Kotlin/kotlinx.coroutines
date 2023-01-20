/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlin.coroutines.*
import kotlin.test.*

class MultithreadedDispatcherStressTest {

    private val n = (if (isNative) 1_000 else 10_000) * stressTestMultiplier
    val shared = atomic(0)

    /**
     * Tests that [newFixedThreadPoolContext] will not drop tasks when closed.
     */
    @Test
    fun testClosingNotDroppingTasks() {
        repeat(7) {
            shared.value = 0
            val nThreads = it + 1
            val dispatcher = newFixedThreadPoolContext(nThreads, "testMultiThreadedContext")
            repeat(n) {
                dispatcher.dispatch(EmptyCoroutineContext, Runnable {
                    shared.incrementAndGet()
                })
            }
            dispatcher.close()
            val m = shared.value
            assertEquals(n, m, "$nThreads threads")
        }
    }
}
