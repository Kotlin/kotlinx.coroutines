package kotlinx.coroutines

import kotlin.test.Test
import kotlin.test.assertEquals

class ScheduleTest : TestBase() {

    @Test
    fun testScheduleExecutesBlockAfterGivenDelay() = runTest {
        expect(1)
        val result = scheduleAsync(50) {
            expect(3)
            "OK"
        }
        expect(2)
        delay(100)
        finish(4)
        assertEquals("OK", result.await())
    }

    @Test
    fun testScheduleNotExecutingBlockIfCanceled() = runTest {
        expect(1)
        val job = scheduleAsync(1000) {
            expectUnreached()
        }
        expect(2)
        job.cancelAndJoin()
        finish(3)
    }

    @Test
    fun testRunningBlockNotCanceledIfScheduledWithNonCancelableContext() = runTest {
        expect(1)
        val job = scheduleAsync(50, NonCancellable) {
            delay(100)
            expect(4)
        }
        expect(2)
        delay(75)
        expect(3)
        job.cancelAndJoin()
        finish(5)
    }

    @Test
    fun testScheduleWithFixedDelay() = runTest {
        expect(1)
        val job = scheduleWithFixedDelay(0, 100) {
            expect(3)
            delay(100)
        }
        expect(2)
        delay(150)
        job.cancelAndJoin()
        finish(4)
    }

    @Test
    fun testScheduleAtFixedRate() = runTest {
        expect(1)
        var n = 3
        val job = scheduleAtFixedRate(0, 100) {
            expect(n++)
            delay(100)
        }
        expect(2)
        delay(250)
        job.cancelAndJoin()
        finish(6)
    }
}
