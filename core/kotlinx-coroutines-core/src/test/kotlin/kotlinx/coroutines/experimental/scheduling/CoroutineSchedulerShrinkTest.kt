package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import org.junit.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

class CoroutineSchedulerShrinkTest : SchedulerTestBase() {

    private val blockingTasksCount = CORES_COUNT * 3
    private val blockingTasksBarrier = CyclicBarrier(blockingTasksCount + 1)
    lateinit var blocking: CoroutineContext

    @Before
    fun setUp() {
        corePoolSize = CORES_COUNT
        blocking = blockingDispatcher(100)

    }

    @Test(timeout = 15_000)
    fun testShrinkOnlyBlockingTasks() = runBlocking {
        // Init dispatcher
        async(dispatcher) { }.await()
        // Pool is initialized with core size in the beginning
        checkPoolThreadsExist(corePoolSize)

        // Run blocking tasks and check increased threads count
        val blockingTasks = launchBlocking()
        checkBlockingTasks(blockingTasks)

        delay(10, TimeUnit.SECONDS)
        // Pool should shrink to core size +- eps
        checkPoolThreadsExist(corePoolSize..corePoolSize + 3)
    }

    @Test(timeout = 15_000)
    fun testShrinkMixedWithWorkload() = runBlocking {
        // Block blockingTasksCount cores in blocking dispatcher
        val blockingTasks = launchBlocking()

        // Block cores count CPU threads
        val nonBlockingBarrier = CyclicBarrier(CORES_COUNT + 1)
        val nonBlockingTasks = (1..CORES_COUNT).map {
            async(dispatcher) {
                nonBlockingBarrier.await()
            }
        }

        // Check CPU tasks succeeded properly even though blocking tasks acquired everything
        nonBlockingTasks.forEach { require(it.isActive) }
        nonBlockingBarrier.await()
        nonBlockingTasks.joinAll()

        // Check blocking tasks succeeded properly
        checkBlockingTasks(blockingTasks)

        delay(10, TimeUnit.SECONDS)
        // Pool should shrink to core size
        checkPoolThreadsExist(corePoolSize..corePoolSize + 3)
    }

    private suspend fun checkBlockingTasks(blockingTasks: List<Deferred<*>>) {
        checkPoolThreadsExist(blockingTasksCount..corePoolSize + blockingTasksCount)
        blockingTasksBarrier.await()
        blockingTasks.joinAll()
    }

    @Test(timeout = 15_000)
    @Ignore // flaky and non deterministic
    fun testShrinkWithExternalTasks() = runBlocking {
        val nonBlockingBarrier = CyclicBarrier(CORES_COUNT + 1)
        val blockingTasks = launchBlocking()

        val nonBlockingTasks = (1..CORES_COUNT).map {
            async(dispatcher) {
                nonBlockingBarrier.await()
            }
        }

        // Tasks that burn CPU. Delay is important so tasks will be scheduled from external thread
        val busySpinTasks = (1..2).map {
            async(dispatcher) {
                while (true) {
                    delay(100, TimeUnit.MICROSECONDS)
                    yield()
                }
            }
        }

        nonBlockingTasks.forEach { require(it.isActive) }
        nonBlockingBarrier.await()
        nonBlockingTasks.joinAll()

        checkBlockingTasks(blockingTasks)

        delay(10, TimeUnit.SECONDS)
        // Pool should shrink almost to core size (+/- eps)
        checkPoolThreadsExist(CORES_COUNT..CORES_COUNT + 4)

        busySpinTasks.forEach {
            require(it.isActive)
            it.cancelAndJoin()
        }
    }

    private suspend fun launchBlocking(): List<Deferred<*>> {
        val result = (1..blockingTasksCount).map {
            async(blocking) {
                blockingTasksBarrier.await()
            }
        }

        while (blockingTasksBarrier.numberWaiting != blockingTasksCount) {
            delay(1)
        }

        return result
    }
}
