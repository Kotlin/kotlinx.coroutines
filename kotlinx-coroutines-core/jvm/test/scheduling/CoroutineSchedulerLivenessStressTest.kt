package kotlinx.coroutines.scheduling

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.scheduling.CoroutineScheduler.Companion.MAX_SUPPORTED_POOL_SIZE
import org.junit.*
import java.util.concurrent.*

class CoroutineSchedulerLivenessStressTest : TestBase() {
    private val scheduler = lazy { CoroutineScheduler(CORE_POOL_SIZE, MAX_SUPPORTED_POOL_SIZE, Long.MAX_VALUE) }
    private val iterations = 1000 * stressTestMultiplier

    @After
    fun tearDown() {
        if (scheduler.isInitialized()) {
            scheduler.value.close()
        }
    }

    @Test
    fun testInternalSubmissions() {
        Assume.assumeTrue(CORE_POOL_SIZE >= 2)
        repeat(iterations) {
            val barrier = CyclicBarrier(CORE_POOL_SIZE + 1)
            scheduler.value.execute {
                repeat(CORE_POOL_SIZE) {
                    scheduler.value.execute {
                        barrier.await()
                    }
                }
            }
            barrier.await()
        }
    }

    @Test
    fun testExternalSubmissions() {
        Assume.assumeTrue(CORE_POOL_SIZE >= 2)
        repeat(iterations) {
            val barrier = CyclicBarrier(CORE_POOL_SIZE + 1)
            repeat(CORE_POOL_SIZE) {
                scheduler.value.execute {
                    barrier.await()
                }
            }
            barrier.await()
        }
    }
}
