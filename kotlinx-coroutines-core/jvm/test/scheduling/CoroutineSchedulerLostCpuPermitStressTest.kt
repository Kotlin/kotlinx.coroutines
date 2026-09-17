package kotlinx.coroutines.scheduling

import kotlinx.coroutines.testing.*
import java.util.concurrent.*
import kotlin.random.Random
import kotlin.test.*

class CoroutineSchedulerLostCpuPermitStressTest: TestBase() {

    // See https://github.com/Kotlin/kotlinx.coroutines/issues/4491
    @Test
    fun testLostCpuPermit() {
        // Sometimes, this test passes after a million iterations with the bug present!
        val iterations = 100_000 * stressTestMultiplier
        CoroutineScheduler(1, 2, Long.MAX_VALUE).use { scheduler ->
            repeat(iterations) {
                // Start a CPU worker
                val cpuLatch = CountDownLatch(1)
                scheduler.dispatch({
                    cpuLatch.countDown()
                }, NonBlockingContext, false)
                val cpuInitiallyAvailable = cpuLatch.await(1, TimeUnit.SECONDS)
                assertTrue(cpuInitiallyAvailable, "Failed to start CPU worker on iteration $it")
                // The CPU worker has finished its task and put itself on the stack.
                // Spawn another worker on top of it.
                val ioLatch = CountDownLatch(1)
                scheduler.dispatch({
                    ioLatch.countDown()
                }, BlockingContext, false)
                ioLatch.await()
                val finalLatch = CountDownLatch(1)
                scheduler.dispatch({
                    finalLatch.countDown()
                }, NonBlockingContext, false)
                val cpuAvailableAfterBlocking = finalLatch.await(1, TimeUnit.SECONDS)
                assertTrue(cpuAvailableAfterBlocking, "Lost CPU permit on iteration $it")
            }
        }
    }
}
