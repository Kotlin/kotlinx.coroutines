package kotlinx.coroutines.experimental

import org.junit.*
import org.junit.Test
import java.io.*
import java.util.concurrent.*
import kotlin.test.*

class JoinStressTest : TestBase() {

    private val iterations = 50_000 * stressTestMultiplier
    private val pool = newFixedThreadPoolContext(3, "JoinStressTest")

    @After
    fun tearDown() {
        pool.close()
    }

    class TestException : Exception() {
        override fun fillInStackTrace(): Throwable = this
    }

    @Test
    fun testExceptionalJoinWithCancellation() = runBlocking {
        val results = IntArray(2)

        repeat(iterations) {
            val barrier = CyclicBarrier(3)
            val exceptionalJob = async(pool) {
                barrier.await()
                throw TestException()
            }


            val awaiterJob = async(pool) {
                barrier.await()
                try {
                    exceptionalJob.await()
                } catch (e: TestException) {
                    0
                } catch (e: CancellationException) {
                    1
                }
            }

            barrier.await()
            exceptionalJob.cancel()
            ++results[awaiterJob.await()]
            require(!exceptionalJob.cancel())
        }

        // Check that concurrent cancellation of job which throws TestException without suspends doesn't suppress TestException
        assertEquals(iterations, results[0], results.toList().toString())
        assertEquals(0, results[1], results.toList().toString())
    }

    @Test
    fun testExceptionalJoinWithMultipleCancellations() = runBlocking {
        val results = IntArray(2)
        var successfulCancellations = 0

        repeat(iterations) {
            val barrier = CyclicBarrier(4)
            val exceptionalJob = async(pool) {
                barrier.await()
                throw TestException()
            }

            val awaiterJob = async(pool) {
                barrier.await()
                try {
                    exceptionalJob.await()
                } catch (e: TestException) {
                    0
                } catch (e: CancellationException) {
                    1
                }
            }

            val canceller = async(pool) {
                barrier.await()
                exceptionalJob.cancel(IOException())
            }

            barrier.await()
            val result = exceptionalJob.cancel()
            ++results[awaiterJob.await()]
            val cancellerResult = canceller.await()

            // None or one cancel can succeed
            require(!(result && cancellerResult))
            require(!exceptionalJob.cancel())

            if (result || cancellerResult) {
                ++successfulCancellations
            }
        }

        assertEquals(iterations, results[0], results.toList().toString())
        assertEquals(0, results[1], results.toList().toString())
        require(successfulCancellations > 0) { "Cancellation never succeeds, something wrong with stress test infra" }
    }
}
