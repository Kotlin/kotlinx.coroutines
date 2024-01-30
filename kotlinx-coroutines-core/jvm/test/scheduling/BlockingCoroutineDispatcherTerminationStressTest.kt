package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.scheduling.*
import org.junit.*
import java.util.*
import java.util.concurrent.*

class BlockingCoroutineDispatcherTerminationStressTest : TestBase() {
    private val baseDispatcher = SchedulerCoroutineDispatcher(
        2, 20,
        TimeUnit.MILLISECONDS.toNanos(10)
    )
    private val ioDispatcher = baseDispatcher.blocking()
    private val TEST_SECONDS = 3L * stressTestMultiplier

    @After
    fun tearDown() {
        baseDispatcher.close()
    }

    @Test
    fun testTermination() {
        val rnd = Random()
        val deadline = System.currentTimeMillis() + TimeUnit.SECONDS.toMillis(TEST_SECONDS)
        while (System.currentTimeMillis() < deadline) {
            Thread.sleep(rnd.nextInt(30).toLong())
            repeat(rnd.nextInt(5) + 1) {
                GlobalScope.launch(ioDispatcher) {
                    Thread.sleep(rnd.nextInt(5).toLong())
                }
            }
        }
    }
}
