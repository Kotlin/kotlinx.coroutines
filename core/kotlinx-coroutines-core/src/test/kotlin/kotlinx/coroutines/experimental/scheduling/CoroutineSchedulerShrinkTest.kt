package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import org.junit.*
import java.util.concurrent.*

class CoroutineSchedulerShrinkTest : SchedulerTestBase() {


    @Test(timeout = 10_000)
    fun testShrinkOnlyBlockingTasks() = runBlocking {
        corePoolSize = CORES_COUNT
        val tasksCount = 24

        // Init dispatcher
        async(dispatcher) { }.await()

        // Pool is initialized with core size in the beginning
        checkPoolThreadsExist(CORES_COUNT)

        // Launch only blocking tasks
        val latch = CountDownLatch(1)
        val blocking = blockingDispatcher(100)
        val blockingTasks = (1..tasksCount).map {
            async(blocking) {
                latch.await()
            }
        }

        //At least #tasksCount threads should be created
        checkPoolThreadsExist(tasksCount..CORES_COUNT + tasksCount)
        latch.countDown()
        blockingTasks.joinAll()

        delay(5, TimeUnit.SECONDS)
        // Pool should shrink to core size
        checkPoolThreadsExist(CORES_COUNT)
    }

    @Test(timeout = 10_000)
    fun testShrinkMixedWithWorkload() = runBlocking {
        corePoolSize = CORES_COUNT
        val tasksCount = 24

        // Launch only blocking tasks
        val latch = CountDownLatch(1)
        val blocking = blockingDispatcher(100)
        val blockingTasks = (1..tasksCount).map {
            async(blocking) {
                latch.await()
            }
        }

        val nonBlockingBarrier = CyclicBarrier(CORES_COUNT + 1)
        val nonBlockingTasks = (1..CORES_COUNT).map {
            async(dispatcher) {
                nonBlockingBarrier.await()
            }
        }

        nonBlockingTasks.forEach { require(it.isActive) }
        nonBlockingBarrier.await()
        nonBlockingTasks.joinAll()

        //At least #tasksCount threads should be created
        checkPoolThreadsExist(tasksCount..CORES_COUNT + tasksCount)
        latch.countDown()
        blockingTasks.joinAll()

        delay(5, TimeUnit.SECONDS)
        // Pool should shrink to core size
        checkPoolThreadsExist(CORES_COUNT)
    }

    @Ignore
    @Test(timeout = 15_000)
    fun testShrinkWithActiveWork() = runBlocking {
        corePoolSize = CORES_COUNT
        val tasksCount = 24

        val latch = CountDownLatch(1)
        val nonBlockingBarrier = CyclicBarrier(CORES_COUNT + 1)
        val blocking = blockingDispatcher(100)

        val blockingTasks = (1..tasksCount).map {
            async(blocking) {
                latch.await()
            }
        }

        val nonBlockingTasks = (1..CORES_COUNT).map {
            async(dispatcher) {
                nonBlockingBarrier.await()
            }
        }

        val busySpinTasks = (1..2).map {
            // TODO for lower resolution pool shrinks much slower
            async(dispatcher) { while (true) delay(1) }
        }

        nonBlockingTasks.forEach { require(it.isActive) }
        nonBlockingBarrier.await()

        // At least #tasksCount threads should be created
        checkPoolThreadsExist(CORES_COUNT + tasksCount)

        latch.countDown()
        blockingTasks.joinAll()
        nonBlockingTasks.joinAll()

        delay(10, TimeUnit.SECONDS)
        // Pool should shrink to core size
        checkPoolThreadsExist(CORES_COUNT)

        busySpinTasks.forEach {
            require(it.isActive)
            it.cancelAndJoin()
        }
    }
}
