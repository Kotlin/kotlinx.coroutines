package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.*

class TestBaseTest : TestBase() {
    @Test
    fun testThreadsShutdown() {
        repeat(1000 * stressTestMultiplier) { _ ->
            initPoolsBeforeTest()
            val threadsBefore = currentThreads()
            runBlocking {
                val sub = launch {
                    delay(10000000L)
                }
                sub.cancel()
                sub.join()
            }
            shutdownPoolsAfterTest()
            checkTestThreads(threadsBefore)
        }

    }
}