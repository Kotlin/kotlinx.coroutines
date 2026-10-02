@file:OptIn(ExperimentalAtomicApi::class)
package kotlinx.coroutines.scheduling

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import java.util.concurrent.*
import kotlin.concurrent.atomics.*
import kotlin.test.*

class BlockingCoroutineDispatcherThreadLimitStressTest : SchedulerTestBase() {

    init {
        corePoolSize = CORES_COUNT
    }

    private val observedParallelism = ConcurrentHashMap<Int, Boolean>().keySet(true)
    private val concurrentWorkers = AtomicInt(0)

    @Test
    fun testLimitParallelismToOne() = runTest {
        val limitingDispatcher = blockingDispatcher(1)
        // Do in bursts to avoid OOM
        repeat(100 * stressTestMultiplierSqrt) {
            val iterations = 1_000 * stressTestMultiplierSqrt
            val tasks = (1..iterations).map {
                async(limitingDispatcher) {
                    try {
                        val currentlyExecuting = concurrentWorkers.incrementAndFetch()
                        observedParallelism.add(currentlyExecuting)
                    } finally {
                        concurrentWorkers.decrement()
                    }
                }
            }
            tasks.joinAll()
            assertEquals(1, observedParallelism.single(), "Expected parallelism should be 1, had $observedParallelism")
        }
    }

    @Test
    fun testLimitParallelism() = runBlocking {
        val limitingDispatcher = blockingDispatcher(CORES_COUNT)
        val iterations = 50_000 * stressTestMultiplier
        val tasks = (1..iterations).map {
            async(limitingDispatcher) {
                try {
                    val currentlyExecuting = concurrentWorkers.incrementAndFetch()
                    observedParallelism.add(currentlyExecuting)
                } finally {
                    concurrentWorkers.decrement()
                }
            }
        }
        tasks.joinAll()
        assertTrue(observedParallelism.max() <= CORES_COUNT, "Unexpected state: $observedParallelism")
    }
}
