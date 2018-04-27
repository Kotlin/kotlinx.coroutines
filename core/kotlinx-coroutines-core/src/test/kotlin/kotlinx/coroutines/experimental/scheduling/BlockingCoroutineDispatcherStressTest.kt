package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.runner.*
import org.junit.runners.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*

@RunWith(Parameterized::class)
class BlockingCoroutineDispatcherStressTest(private val limit: Int) : SchedulerTestBase() {

    companion object {
        @Parameterized.Parameters(name = "parallelism = {0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = (1..CORES_COUNT).map { arrayOf<Any>(it) }
    }

    init {
        corePoolSize = CORES_COUNT
    }

    private val observedConcurrency = ConcurrentHashMap<Int, Boolean>()
    private val concurrentWorkers = AtomicInteger(0)

    @Test
    fun testLimitParallelism() = runBlocking {
        val limitingDispatcher = blockingDispatcher(limit)
        val iterations = 50_000 * stressTestMultiplier
        val tasks = (1..iterations).map {
            async(limitingDispatcher) {
                try {
                    val currentlyExecuting = concurrentWorkers.incrementAndGet()
                    observedConcurrency[currentlyExecuting] = true
                    require(currentlyExecuting <= limit)
                } finally {
                    concurrentWorkers.decrementAndGet()
                }
            }
        }

        tasks.forEach { it.await() }
        require(tasks.isNotEmpty())
        // Simple sanity, test is too short to guarantee that every possible state was observed
        require(observedConcurrency.size >= 3.coerceAtMost(limit))
        for (i in limit + 1..limit * 2) {
            require(i !in observedConcurrency.keys) { "Unexpected state: $observedConcurrency" }
        }

        checkPoolThreadsCreated(limit..limit + CORES_COUNT * 2)
    }

    @Test
    fun testCpuStarvation() = runBlocking {
        corePoolSize = limit
        val iterations = 100 * stressTestMultiplier

        repeat(iterations) {
            // Create new dispatcher every iteration to increase probability of race
            val dispatcher = ExperimentalCoroutineDispatcher(limit)
            val blockingDispatcher = dispatcher.blocking(100)

            val blockingLatch = CountDownLatch(1)
            val cpuBarrier = CyclicBarrier(limit + 1)

            val cpuTasks = CopyOnWriteArrayList<Deferred<*>>()
            val blockingTasks = CopyOnWriteArrayList<Deferred<*>>()

            repeat(limit) {
                async(dispatcher) {
                    // These two will be stolen first
                    blockingTasks += async(blockingDispatcher) { blockingLatch.await()  }
                    blockingTasks += async(blockingDispatcher) { blockingLatch.await()  }


                    // Empty on CPU job which should be executed while blocked tasks are hang
                    cpuTasks += async(dispatcher) { cpuBarrier.await() }

                    // Block with next task. Block cores * 3 threads in total
                    blockingTasks += async(blockingDispatcher) { blockingLatch.await() }
                }
            }

            cpuTasks.forEach { require(it.isActive) }
            cpuBarrier.await()
            cpuTasks.forEach { it.await() }
            blockingTasks.forEach { require(it.isActive) }
            blockingLatch.countDown()
            blockingTasks.forEach { it.await() }
            dispatcher.close()
        }
    }
}
