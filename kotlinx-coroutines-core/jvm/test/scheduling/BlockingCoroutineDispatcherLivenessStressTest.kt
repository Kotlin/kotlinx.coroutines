@file:OptIn(ExperimentalAtomicApi::class)
package kotlinx.coroutines.scheduling

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.concurrent.atomics.*
import kotlin.test.*

/**
 * Test that ensures implementation correctness of [kotlinx.coroutines.internal.LimitedDispatcher] and
 * designed to stress its particular implementation details.
 */
class BlockingCoroutineDispatcherLivenessStressTest : SchedulerTestBase() {
    private val concurrentWorkers = AtomicInt(0)

    @BeforeTest
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
            coroutineScope {
                (1..2).forEach {
                    launch(limitingDispatcher) {
                        try {
                            val currentlyExecuting = concurrentWorkers.incrementAndFetch()
                            assertEquals(1, currentlyExecuting)
                        } finally {
                            concurrentWorkers.decrement()
                        }
                    }
                }
            }
        }
    }

    @Test
    fun testPingPongThreadsCount() = runBlocking {
        corePoolSize = CORES_COUNT
        val iterations = 100_000 * stressTestMultiplier
        val completed = AtomicInt(0)
        for (i in 1..iterations) {
            coroutineScope {
                (1..2).forEach {
                    launch(dispatcher) {
                        // Useless work
                        concurrentWorkers.increment()
                        concurrentWorkers.decrement()
                        completed.increment()
                    }
                }
            }
        }
        assertEquals(2 * iterations, completed.load())
    }
}
