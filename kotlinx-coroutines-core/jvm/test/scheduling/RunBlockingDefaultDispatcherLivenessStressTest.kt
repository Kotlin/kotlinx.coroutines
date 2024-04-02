package scheduling

import kotlinx.coroutines.testing.*
import org.junit.*
import org.junit.runner.*
import org.junit.runners.*

@RunWith(Parameterized::class)
class RunBlockingDefaultDispatcherLivenessStressTest(private val yieldMask: Int) : RunBlockingCoroutineSchedulerLivenessTestBase() {
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
    fun testLivenessOfDefaultDispatcher(): Unit = testSchedulerLiveness(dispatcher, yieldMask)
}