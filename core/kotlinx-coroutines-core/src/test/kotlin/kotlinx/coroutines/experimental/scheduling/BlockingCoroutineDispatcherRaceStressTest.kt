package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.async
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Test
import java.util.concurrent.atomic.AtomicInteger

class BlockingCoroutineDispatcherRaceStressTest : SchedulerTestBase() {
    private var limitingDispatcher = blockingDispatcher(1)
    private val concurrentWorkers = AtomicInteger(0)


    @Test(timeout = 20_000L)
    fun testAddPollRace() = runBlocking {
        // Stress test for specific case (race #2 from LimitingDispatcher). Shouldn't hang.
        for (i in 1..100_000) {
            val tasks = (1..2).map {
                async(limitingDispatcher) {
                    try {
                        val currentlyExecuting = concurrentWorkers.incrementAndGet()
                        require(currentlyExecuting == 1)
                    } finally {
                        concurrentWorkers.decrementAndGet()
                    }
                }
            }

            tasks.forEach { it.await() }
        }

        checkPoolThreads(2..3)
    }
}