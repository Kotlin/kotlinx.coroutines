package scheduling

import kotlinx.coroutines.testing.*
import org.junit.*
import org.junit.runner.*
import org.junit.runners.*

@RunWith(Parameterized::class)
class RunBlockingLimitedDispatcherLivenessStressTest(private val yieldMask: Int) : RunBlockingCoroutineSchedulerLivenessTestBase() {
    init {
        corePoolSize = 1
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters
        fun data(): Array<Array<Any?>> {
            return Array(32 * stressTestMultiplierSqrt) { arrayOf(it) }
        }
    }

    @Test
    fun testLivenessOfLimitedDispatcherOnTopOfDefaultDispatcher() =
        testSchedulerLiveness(dispatcher.limitedParallelism(1), yieldMask)

    @Test
    fun testLivenessOfLimitedDispatcherOnTopOfIoDispatcher() = testSchedulerLiveness(
        // Important: inner limitedDispatcher will be on top of this LimitedDispatcher, so there are two Workers from
        // two different LimitedDispatchers that must coordinate their permits, not just one.
        // In other words, LimitedDispatcher's Worker should also respect BlockingDispatchAware on its inner tasks
        blockingDispatcher.value.limitedParallelism(1), yieldMask
    )
}