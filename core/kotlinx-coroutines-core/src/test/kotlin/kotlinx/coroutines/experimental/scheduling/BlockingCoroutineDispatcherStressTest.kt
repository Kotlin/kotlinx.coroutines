package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.async
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger

@RunWith(Parameterized::class)
class BlockingCoroutineDispatcherStressTest(private val limit: Int) : SchedulerTestBase() {

    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = (1..Runtime.getRuntime().availableProcessors()).map { arrayOf<Any>(it) }
    }

    init {
        corePoolSize = CORES_COUNT
    }

    private var limitingDispatcher = blockingDispatcher(limit)
    private val observedConcurrency = ConcurrentHashMap<Int, Boolean>()
    private val concurrentWorkers = AtomicInteger(0)


    @Test(timeout = 20_000L)
    fun testLimitParallelism() = runBlocking {
        val tasks = (1..250_000).map {
            async(limitingDispatcher) {
                try {
                    val currentlyExecuting = concurrentWorkers.incrementAndGet()
                    observedConcurrency[currentlyExecuting] = true
                    require(currentlyExecuting <= limit)
                } finally {
                    concurrentWorkers.decrementAndGet()
                }
            }
        }

        tasks.forEach { it.await() }
        require(tasks.isNotEmpty())
        // Simple sanity, test is too short to guarantee that every possible state was observed
        require(observedConcurrency.size >= 3.coerceAtMost(limit))
        for (i in limit + 1..limit * 2) {
            require(i !in observedConcurrency.keys, { "Unexpected state: $observedConcurrency" })
        }

        val lowerBound = Runtime.getRuntime().availableProcessors() + limit
        checkPoolThreads(lowerBound..lowerBound + Runtime.getRuntime().availableProcessors())
    }
}