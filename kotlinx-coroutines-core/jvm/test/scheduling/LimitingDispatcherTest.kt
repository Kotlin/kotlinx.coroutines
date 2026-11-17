package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.*
import java.util.concurrent.*
import kotlin.test.assertFailsWith
import kotlin.concurrent.atomics.*

@OptIn(ExperimentalAtomicApi::class)
class LimitingDispatcherTest : SchedulerTestBase() {

    @Test
    fun testNegativeView() {
        assertFailsWith<IllegalArgumentException> { view(-1) }
    }

    @Test
    fun testZeroView() {
        assertFailsWith<IllegalArgumentException> { view(0) }
    }

    @Test(timeout = 10_000)
    fun testBlockingInterleave() = runBlocking {
        corePoolSize = 3
        val view = view(2)
        val blocking = blockingDispatcher(4)
        val barrier = CyclicBarrier(6)
        val tasks = ArrayList<Job>(6)
        repeat(2) {
            tasks += async(view) {
                barrier.await()
            }

            repeat(2) {
                tasks += async(blocking) {
                    barrier.await()
                }
            }
        }

        tasks.joinAll()
    }

    /** Tests that saturating [Dispatchers.Default] with limited dispatcher workers still allows other tasks to run. */
    @Test(timeout = 10_000)
    fun testDefaultFairness() = runBlocking<Unit> {
        corePoolSize = 2
        val entered = AtomicBoolean(false)
        val firstViewStarted = CountDownLatch(1)
        launch(view(1)) {
            firstViewStarted.countDown()
            while (!entered.load()) {
                yield()
            }
        }
        launch(view(1)) {
            yield()
            firstViewStarted.await()
            launch(dispatcher) {
                entered.store(true)
            }
            while (!entered.load()) {
                yield()
            }
        }
    }
}
