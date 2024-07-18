package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.Test
import java.lang.Runnable
import java.util.concurrent.*
import kotlin.test.*

class ExecutorAsCoroutineDispatcherDelayTest : TestBase() {

    private var callsToSchedule = 0

    private inner class STPE : ScheduledThreadPoolExecutor(1) {
        override fun schedule(command: Runnable, delay: Long, unit: TimeUnit): ScheduledFuture<*> {
            if (delay != 0L) ++callsToSchedule
            return super.schedule(command, delay, unit)
        }
    }

    private inner class SES : ScheduledExecutorService by STPE()

    @Test
    fun testScheduledThreadPool() = runTest {
        val executor = STPE()
        withContext(executor.asCoroutineDispatcher()) {
            delay(100)
        }
        executor.shutdown()
        assertEquals(1, callsToSchedule)
    }

    @Test
    fun testScheduledExecutorService() = runTest {
        val executor = SES()
        withContext(executor.asCoroutineDispatcher()) {
            delay(100)
        }
        executor.shutdown()
        assertEquals(1, callsToSchedule)
    }

    @Test
    fun testCancelling() = runTest {
        val executor = STPE()
        launch(start = CoroutineStart.UNDISPATCHED) {
            suspendCancellableCoroutine<Unit> { cont ->
                expect(1)
                (executor.asCoroutineDispatcher() as Delay).scheduleResumeAfterDelay(1_000_000, cont)
                cont.cancel()
                expect(2)
            }
        }
        expect(3)
        assertTrue(executor.getQueue().isEmpty())
        executor.shutdown()
        finish(4)
    }
}
