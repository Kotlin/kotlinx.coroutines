package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class AwaitStressTest : TestBase() {

    private val iterations = 50_000 * stressTestMultiplier

    @Test
    fun testMultipleExceptions() = runTest {
        newFixedThreadPoolContext(4, "test").use { pool ->
            val ctx = pool + NonCancellable
            repeat(iterations) {
                val barrier = ConcurrentCyclicBarrier(4)
                val d1 = async(ctx) {
                    barrier.await()
                    throw TestException()
                }
                val d2 = async(ctx) {
                    barrier.await()
                    throw TestException()
                }
                val d3 = async(ctx) {
                    barrier.await()
                    1L
                }
                try {
                    barrier.await()
                    awaitAll(d1, d2, d3)
                    expectUnreached()
                } catch (_: TestException) {
                    // Expected behavior
                }
            }
        }
    }

    @Test
    fun testAwaitAll() = runTest {
        newFixedThreadPoolContext(4, "test").use { pool ->
            val barrier = ConcurrentCyclicBarrier(3)
            repeat(iterations) {
                val d1 = async(pool) {
                    barrier.await()
                    1L
                }
                val d2 = async(pool) {
                    barrier.await()
                    2L
                }
                barrier.await()
                awaitAll(d1, d2)
                require(d1.isCompleted && d2.isCompleted)
            }
        }
    }

    @Test
    fun testConcurrentCancellation() = runTest {
        newFixedThreadPoolContext(4, "test").use { pool ->
            var cancelledOnce = false
            repeat(iterations) {
                val barrier = ConcurrentCyclicBarrier(3)

                val d1 = async(pool) {
                    barrier.await()
                    delay(10_000)
                    yield()
                }

                val d2 = async(pool) {
                    barrier.await()
                    d1.cancel()
                }

                barrier.await()
                try {
                    awaitAll(d1, d2)
                } catch (_: CancellationException) {
                    cancelledOnce = true
                }
            }

            require(cancelledOnce) { "Cancellation exception wasn't properly caught" }
        }
    }
}
