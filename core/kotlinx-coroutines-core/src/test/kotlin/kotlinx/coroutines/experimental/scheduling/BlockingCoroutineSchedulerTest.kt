package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.yield
import org.junit.Test
import java.util.concurrent.CyclicBarrier

class BlockingCoroutineSchedulerTest : SchedulerTestBase() {

    @Test(timeout = 1_000)
    fun testNonBlockingWithBlockingExternal() = runBlocking {
        val barrier = CyclicBarrier(2)

        val blockingJob = launch(blockingDispatcher.value) {
            barrier.await()
        }

        val nonBlockingJob = launch(dispatcher) {
            barrier.await()
        }

        nonBlockingJob.join()
        blockingJob.join()
        checkPoolThreads(2)
    }

    @Test(timeout = 10_000)
    fun testNonBlockingFromBlocking() = runBlocking {
        val barrier = CyclicBarrier(2)

        val blocking = launch(blockingDispatcher.value) {
            // This task will be stolen
            launch(dispatcher) {
                barrier.await()
            }

            barrier.await()
        }

        blocking.join()
        checkPoolThreads(2)
    }

    @Test(timeout = 1_000)
    fun testScheduleBlockingThreadCount() = runTest {
        // After first iteration pool is idle, repeat, no new threads should be created
        repeat(2) {
            val blocking = launch(blockingDispatcher.value) {
                launch(blockingDispatcher.value) {
                }
            }

            blocking.join()
            // Depends on how fast thread will be created
            checkPoolThreads(2..3)
        }
    }

    @Test(timeout = 1_000)
    fun testNoExcessContextSwitches() = runTest {
        val job = launch(dispatcher) {
            val thread = Thread.currentThread()

            val blockingJob = launch(blockingDispatcher.value) {
                require(thread === Thread.currentThread())
            }

            blockingJob.join()
            require(thread === Thread.currentThread())
        }

        job.join()
    }

    @Test(timeout = 1_000)
    fun testNoCpuStarvation() = runBlocking {
        val tasksNum = 100
        val barrier = CyclicBarrier(tasksNum + 1)
        val tasks = (1..tasksNum).map { launch(blockingDispatcher.value) { barrier.await() } }

        val cpuTask = launch(dispatcher) {
            // Do nothing, just complete
        }

        cpuTask.join()
        tasks.forEach { require(it.isActive) }
        barrier.await()
        tasks.joinAll()
        checkPoolThreads(101)
    }

    @Test(timeout = 1_000)
    fun testNoCpuStarvationWithMultipleBlockingContexts() = runBlocking {
        val firstBarrier = CyclicBarrier(11)
        val secondBarrier = CyclicBarrier(11)
        val blockingDispatcher = blockingDispatcher(10)
        val blockingDispatcher2 = blockingDispatcher(10)

        val blockingTasks = (1..10).flatMap {
            listOf(launch(blockingDispatcher) { firstBarrier.await() }, launch(blockingDispatcher2) { secondBarrier.await() })
        }

        val cpuTasks = (1..100).map {
            launch(dispatcher) {
                // Do nothing, just complete
            }
        }.toList()

        cpuTasks.joinAll()
        blockingTasks.forEach { require(it.isActive) }
        firstBarrier.await()
        secondBarrier.await()
        blockingTasks.joinAll()
        checkPoolThreads(21..21 + CORES_COUNT)
    }

    @Test(timeout = 1_000)
    fun testNoExcessThreadsCreated() = runBlocking {
        corePoolSize = 4

        val tasksNum = 100
        val barrier = CyclicBarrier(tasksNum + 1)
        val blockingTasks = (1..tasksNum).map { launch(blockingDispatcher.value) { barrier.await() } }

        val nonBlockingTasks = (1..tasksNum).map {
            launch(dispatcher) {
                yield()
            }
        }

        nonBlockingTasks.joinAll()
        barrier.await()
        blockingTasks.joinAll()
        // There may be race when multiple CPU threads are trying to lazily created one more
        checkPoolThreads(104..110)
    }

    @Test
    fun testBlockingFairness() = runBlocking {

    }

    @Test(expected = IllegalArgumentException::class)
    fun testNegativeParallelism() {
        blockingDispatcher(-1)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testZeroParallelism() {
        blockingDispatcher(0)
    }
}