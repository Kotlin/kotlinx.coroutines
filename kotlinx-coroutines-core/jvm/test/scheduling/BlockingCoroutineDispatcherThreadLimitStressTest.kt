/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.Ignore
import org.junit.Test
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.test.*

class BlockingCoroutineDispatcherThreadLimitStressTest : SchedulerTestBase() {

    init {
        corePoolSize = CORES_COUNT
    }

    private val observedConcurrency = ConcurrentHashMap<Int, Boolean>()
    private val concurrentWorkers = AtomicInteger(0)

    @Test
    @Ignore
    fun testLimitParallelismToOne() = runTest {
        val limitingDispatcher = blockingDispatcher(1)
        // Do in bursts to avoid OOM
        repeat(100 * stressTestMultiplierSqrt) {
            val iterations = 1_000 * stressTestMultiplierSqrt
            val tasks = (1..iterations).map {
                async(limitingDispatcher) {
                    try {
                        val currentlyExecuting = concurrentWorkers.incrementAndGet()
                        observedConcurrency[currentlyExecuting] = true
                        assertTrue(currentlyExecuting <= CORES_COUNT)
                    } finally {
                        concurrentWorkers.decrementAndGet()
                    }
                }
            }
            tasks.forEach { it.await() }
            for (i in CORES_COUNT + 1..CORES_COUNT * 2) {
                require(i !in observedConcurrency.keys) { "Unexpected state: $observedConcurrency" }
            }
            checkPoolThreadsCreated(0..CORES_COUNT + 1)
        }
    }

    @Test
    @Ignore
    fun testLimitParallelism() = runBlocking {
        val limitingDispatcher = blockingDispatcher(CORES_COUNT)
        val iterations = 50_000 * stressTestMultiplier
        val tasks = (1..iterations).map {
            async(limitingDispatcher) {
                try {
                    val currentlyExecuting = concurrentWorkers.incrementAndGet()
                    observedConcurrency[currentlyExecuting] = true
                    assertTrue(currentlyExecuting <= CORES_COUNT)
                } finally {
                    concurrentWorkers.decrementAndGet()
                }
            }
        }
        tasks.forEach { it.await() }
        for (i in CORES_COUNT + 1..CORES_COUNT * 2) {
            require(i !in observedConcurrency.keys) { "Unexpected state: $observedConcurrency" }
        }
        checkPoolThreadsCreated(CORES_COUNT..CORES_COUNT * 3)
    }
}