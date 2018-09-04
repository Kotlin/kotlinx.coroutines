/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import org.junit.*
import java.util.concurrent.atomic.*

class BlockingCoroutineDispatcherRaceStressTest : SchedulerTestBase() {
    private val concurrentWorkers = AtomicInteger(0)

    @Before
    fun setUp() {
        // In case of starvation test will hang
        idleWorkerKeepAliveNs = Long.MAX_VALUE
    }

    @Test
    fun testAddPollRace() = runBlocking {
        val limitingDispatcher = blockingDispatcher(1)
        val iterations = 25_000 * stressTestMultiplier
        // Stress test for specific case (race #2 from LimitingDispatcher). Shouldn't hang.
        for (i in 1..iterations) {
            val tasks = (1..2).map {
                async(limitingDispatcher) {
                    try {
                        val currentlyExecuting = concurrentWorkers.incrementAndGet()
                        require(currentlyExecuting == 1)
                    } finally {
                        concurrentWorkers.decrementAndGet()
                    }
                }
            }

            tasks.forEach { it.await() }
        }

        checkPoolThreadsCreated(2..4)
    }

    @Test
    fun testPingPongThreadsCount() = runBlocking {
        corePoolSize = CORES_COUNT
        val iterations = 100_000 * stressTestMultiplier
        // Stress test for specific case (race #2 from LimitingDispatcher). Shouldn't hang.
        for (i in 1..iterations) {
            val tasks = (1..2).map {
                async(dispatcher) {
                    // Useless work
                    concurrentWorkers.incrementAndGet()
                    concurrentWorkers.decrementAndGet()
                }
            }

            tasks.forEach { it.await() }
        }

        checkPoolThreadsCreated(CORES_COUNT)
    }
}
