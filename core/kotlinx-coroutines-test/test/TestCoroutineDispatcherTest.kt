package kotlinx.coroutines.test

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.delay
import kotlinx.coroutines.launch
import org.junit.Test
import java.util.concurrent.TimeUnit
import kotlin.test.assertEquals

class TestCoroutineDispatcherTest {
    @Test
    fun whenStringCalled_itReturnsString() {
        val subject = TestCoroutineDispatcher()
        assertEquals("TestCoroutineDispatcher[time=0ns]", subject.toString())
    }

    @Test
    fun whenStringCalled_itReturnsCurrentTime() {
        val subject = TestCoroutineDispatcher()
        subject.advanceTimeBy(1000, TimeUnit.NANOSECONDS)
        assertEquals("TestCoroutineDispatcher[time=1000ns]", subject.toString())
    }

    @Test
    fun whenCurrentTimeCalled_returnsTimeAsSpecified() {
        val subject = TestCoroutineDispatcher()
        subject.advanceTimeBy(1000, TimeUnit.MILLISECONDS)

        assertEquals(1_000_000_000, subject.currentTime(TimeUnit.NANOSECONDS))
        assertEquals(1_000, subject.currentTime(TimeUnit.MILLISECONDS))
        assertEquals(1, subject.currentTime(TimeUnit.SECONDS))

        assertEquals(1_000, subject.currentTime())
    }

    @Test
    fun whenAdvanceTimeCalled_defaultsToMilliseconds() {
        val subject = TestCoroutineDispatcher()
        subject.advanceTimeBy(1_000)

        assertEquals(1_000, subject.currentTime(TimeUnit.MILLISECONDS))
    }

    @Test
    fun whenAdvanceTimeCalled_respectsTimeUnit() {
        val subject = TestCoroutineDispatcher()
        subject.advanceTimeBy(1, TimeUnit.SECONDS)

        assertEquals(1_000, subject.currentTime(TimeUnit.MILLISECONDS))
    }

    @Test
    fun whenDispatcherPaused_doesntAutoProgressCurrent() {
        val subject = TestCoroutineDispatcher()
        subject.pauseDispatcher()
        val scope = CoroutineScope(subject)
        var executed = 0
        scope.launch {
            executed++
        }
        assertEquals(0, executed)
    }

    @Test
    fun whenDispatcherResumed_doesAutoProgressCurrent() {
        val subject = TestCoroutineDispatcher()
        val scope = CoroutineScope(subject)
        var executed = 0
        scope.launch {
            executed++
        }

        assertEquals(1, executed)
    }

    @Test
    fun whenDispatcherResumed_doesNotAutoProgressTime() {
        val subject = TestCoroutineDispatcher()
        val scope = CoroutineScope(subject)
        var executed = 0
        scope.launch {
            delay(1_000)
            executed++
        }

        assertEquals(0, executed)
        subject.advanceUntilIdle()
        assertEquals(1, executed)
    }

    @Test
    fun whenDispatcherPaused_thenResume_itDoesDispatchCurrent() {
        val subject = TestCoroutineDispatcher()
        subject.pauseDispatcher()
        val scope = CoroutineScope(subject)
        var executed = 0
        scope.launch {
            executed++
        }

        assertEquals(0, executed)
        subject.resumeDispatcher()
        assertEquals(1, executed)
    }

    @Test(expected = UncompletedCoroutinesError::class)
    fun whenDispatcherHasUncompletedCoroutines_itThrowsErrorInCleanup() {
        val subject = TestCoroutineDispatcher()
        subject.pauseDispatcher()
        val scope = CoroutineScope(subject)
        scope.launch {
            delay(1_000)
        }
        subject.cleanupTestCoroutines()
    }
}