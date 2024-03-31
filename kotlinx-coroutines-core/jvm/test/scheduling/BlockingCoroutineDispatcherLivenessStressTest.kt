package kotlinx.coroutines.scheduling

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import java.util.LinkedList
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.test.*

/**
 * Test that ensures implementation correctness of [LimitingDispatcher] and
 * designed to stress its particular implementation details.
 */
class BlockingCoroutineDispatcherLivenessStressTest : SchedulerTestBase() {
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
                        assertEquals(1, currentlyExecuting)
                    } finally {
                        concurrentWorkers.decrementAndGet()
                    }
                }
            }
            tasks.forEach { it.await() }
        }
    }

    @Test
    fun testPingPongThreadsCount() = runBlocking {
        corePoolSize = CORES_COUNT
        val iterations = 100_000 * stressTestMultiplier
        val completed = AtomicInteger(0)
        for (i in 1..iterations) {
            val tasks = (1..2).map {
                async(dispatcher) {
                    // Useless work
                    concurrentWorkers.incrementAndGet()
                    concurrentWorkers.decrementAndGet()
                    completed.incrementAndGet()
                }
            }
            tasks.forEach { it.await() }
        }
        assertEquals(2 * iterations, completed.get())
    }
}

@RunWith(Parameterized::class)
class BlockingCoroutineDispatcherTestCorePoolSize1(private val yieldMask: Int) : SchedulerTestBase() {
    init {
        corePoolSize = 1
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters
        fun data(): Array<Array<Any?>> {
            return Array(10 * stressTestMultiplierSqrt) { arrayOf(it) }
        }
    }

    @Test
    fun testLivenessOfDefaultDispatcher(): Unit = runBlocking {
        val oldRunBlockings = LinkedList<Job>()
        var maxOldRunBlockings = 0
        var busyWaits = 0
        repeat(5000 * stressTestMultiplierSqrt) {
            if (it % 1000 == 0) {
                System.err.println("======== $it, rb=${oldRunBlockings.size}, max rb=${maxOldRunBlockings}, busy=$busyWaits")
            }
            val barrier = CyclicBarrier(2)
            val barrier2 = CompletableDeferred<Unit>()
            val blocking = launch(dispatcher) {
                barrier.await()
                runBlocking {
                    if ((yieldMask and 1) != 0) yield()
                    barrier2.await()
                    if ((yieldMask and 2) != 0) yield()
                }
            }
            oldRunBlockings.addLast(blocking)
            val task = async(dispatcher) {
                if ((yieldMask and 4) != 0) yield()
                42.also {
                    if ((yieldMask and 8) != 0) yield()
                }
            }
            barrier.await()
            task.join()
            barrier2.complete(Unit)

            oldRunBlockings.removeIf(Job::isCompleted)
            while (oldRunBlockings.size > 5) {
                busyWaits++
                oldRunBlockings.removeIf(Job::isCompleted)
            }
            if (oldRunBlockings.size > maxOldRunBlockings) {
                maxOldRunBlockings = oldRunBlockings.size
            }
        }
    }
}
