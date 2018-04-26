package kotlinx.coroutines.experimental

import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class AwaitStressTest : TestBase() {

    private class TestException : Exception() {
        override fun fillInStackTrace(): Throwable = this
    }

    private val iterations = 50_000 * stressTestMultiplier
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

    @Test
    fun testMutatingCollection() = runTest {
        val barrier = CyclicBarrier(4)

        repeat(iterations) {
            // thread-safe collection that we are going to modify
            val deferreds = CopyOnWriteArrayList<Deferred<Long>>()

            deferreds += async(pool) {
                barrier.await()
                1L
            }

            deferreds += async(pool) {
                barrier.await()
                2L
            }

            deferreds += async(pool) {
                barrier.await()
                deferreds.removeAt(2)
                3L
            }

            val allJobs = ArrayList(deferreds)
            barrier.await()
            val results = deferreds.awaitAll() // shouldn't hang
            check(results == listOf(1L, 2L, 3L) || results == listOf(1L, 2L))
            allJobs.awaitAll()
            barrier.reset()
        }
    }
}
