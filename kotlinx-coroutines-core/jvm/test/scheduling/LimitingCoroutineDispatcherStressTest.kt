package kotlinx.coroutines.scheduling

import kotlinx.coroutines.testing.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class LimitingCoroutineDispatcherStressTest : SchedulerTestBase() {

    init {
        corePoolSize = 3
    }

    private val blocking = blockingDispatcher(2)
    private val cpuView = view(2)
    private val cpuView2 = view(2)
    private val concurrentWorkers = atomic(0)
    private val iterations = 25_000 * stressTestMultiplierSqrt

    @Test
    fun testCpuLimitNotExtended() = runBlocking {
        repeat(iterations) {
            launchTask(cpuView2, 3)
            launchTask(cpuView, 3)
        }
    }

    @Test
    fun testCpuLimitWithBlocking() = runBlocking {
        repeat(iterations) {
            launchTask(cpuView, 4)
            launchTask(blocking, 4)
        }
    }

    @IgnorableReturnValue
    private fun CoroutineScope.launchTask(ctx: CoroutineContext, maxLimit: Int) = launch(ctx) {
        try {
            val currentlyExecuting = concurrentWorkers.incrementAndGet()
            assertTrue(currentlyExecuting <= maxLimit, "Executing: $currentlyExecuting, max limit: $maxLimit")
        } finally {
            concurrentWorkers.decrementAndGet()
        }
    }
}
