package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class JobStressTest : TestBase() {
    @Test
    fun testMemoryRelease() {
        val job = Job()
        val n = 10_000_000 * stressTestMultiplier
        var fireCount = 0
        for (i in 0 until n) job.invokeOnCompletion { fireCount++ }.dispose()
    }
}