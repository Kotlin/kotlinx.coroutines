package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.CopyOnWriteArrayList
import java.util.concurrent.CyclicBarrier

class AwaitJvmStressTest : TestBase() {

    private val iterations = 50_000 * stressTestMultiplier
    @get:Rule
    val pool =  ExecutorRule(4)

    @Test
    fun testThreadSafeMutatingCollection() = runTest {
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
            // It is thread-safe to get a snapshot of deferreds while it is being modified for CopyOnWriteArrayList.
            // It is also thread-safe on JVM for any other Collection that implements a thread-safe `toArray`.
            // It is not generally thread-safe on Native.
            // Hence, it's a JVM-only test.
            val results = deferreds.awaitAll() // shouldn't hang
            check(results == listOf(1L, 2L, 3L) || results == listOf(1L, 2L))
            allJobs.awaitAll()
            barrier.reset()
        }
    }
}
