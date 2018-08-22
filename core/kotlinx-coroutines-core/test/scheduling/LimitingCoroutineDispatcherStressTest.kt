package kotlinx.coroutines.experimental.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import org.junit.Test
import kotlin.coroutines.experimental.*
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
    fun testCpuLimitNotExtended() = runBlocking<Unit> {
        val tasks = ArrayList<Deferred<*>>(iterations * 2)
        repeat(iterations) {
            tasks += task(cpuView, 3)
            tasks += task(cpuView2, 3)
        }

        tasks.awaitAll()
    }

    @Test
    fun testCpuLimitWithBlocking() = runBlocking<Unit> {
        val tasks = ArrayList<Deferred<*>>(iterations * 2)
        repeat(iterations) {
            tasks += task(cpuView, 4)
            tasks += task(blocking, 4)
        }

        tasks.awaitAll()
    }

    private fun task(ctx: CoroutineContext, maxLimit: Int): Deferred<Unit> {
        return async(ctx) {
            try {
                val currentlyExecuting = concurrentWorkers.incrementAndGet()
                assertTrue(currentlyExecuting <= maxLimit, "Executing: $currentlyExecuting, max limit: $maxLimit")
            } finally {
                concurrentWorkers.decrementAndGet()
            }
        }
    }
}
