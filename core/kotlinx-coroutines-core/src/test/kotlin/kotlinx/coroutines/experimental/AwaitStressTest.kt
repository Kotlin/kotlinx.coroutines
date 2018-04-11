package kotlinx.coroutines.experimental

import org.junit.After
import java.util.concurrent.CyclicBarrier
import kotlin.test.Test

class AwaitStressTest : TestBase() {

    private class TestException : Exception() {
        override fun fillInStackTrace(): Throwable = this
    }

    private val iterations = 50_000
    private val pool = newFixedThreadPoolContext(4, "AwaitStressTest")

    @After
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testMultipleExceptions() = runTest {

        repeat(iterations) {
            val barrier = CyclicBarrier(4)

            val d1 = async(pool) {
                barrier.await()
                throw TestException()
            }

            val d2 = async(pool) {
                barrier.await()
                throw TestException()
            }

            val d3 = async(pool) {
                barrier.await()
                1L
            }

            try {
                barrier.await()
                awaitAll(d1, d2, d3)
                expectUnreached()
            } catch (e: TestException) {
                // Expected behaviour
            }

            barrier.reset()
        }
    }

    @Test
    fun testAwaitAll() = runTest {
        val barrier = CyclicBarrier(3)

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
            barrier.reset()
        }
    }

    @Test
    fun testConcurrentCancellation() = runTest {
        var cancelledOnce = false
        repeat(iterations) {
            val barrier = CyclicBarrier(3)

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
            } catch (e: JobCancellationException) {
                cancelledOnce = true
            }
        }

        require(cancelledOnce) { "Cancellation exception wasn't properly caught" }
    }
}
