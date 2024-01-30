package kotlinx.coroutines.time

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.Test
import java.time.*
import java.time.temporal.*
import kotlin.test.*

class DurationOverflowTest : TestBase() {

    private val durations = ChronoUnit.values().map { it.duration }

    @Test
    fun testDelay() = runTest {
        var counter = 0
        for (duration in durations) {
            expect(++counter)
            delay(duration.negated()) // Instant bail out from negative values
            launch(start = CoroutineStart.UNDISPATCHED) {
                expect(++counter)
                delay(duration)
            }.cancelAndJoin()
            expect(++counter)
        }

        finish(++counter)
    }

    @Test
    fun testOnTimeout() = runTest {
        for (duration in durations) {
            // Does not crash on overflows
            select<Unit> {
                onTimeout(duration) {}
                onTimeout(duration.negated()) {}
            }
        }
    }

    @Test
    fun testWithTimeout() = runTest {
        for (duration in durations) {
            withTimeout(duration) {}
        }
    }

    @Test
    fun testWithTimeoutOrNull() = runTest {
        for (duration in durations) {
            withTimeoutOrNull(duration) {}
        }
    }

    @Test
    fun testWithTimeoutOrNullNegativeDuration() = runTest {
        val result = withTimeoutOrNull(Duration.ofSeconds(1).negated()) {
            1
        }

        assertNull(result)
    }

    @Test
    fun testZeroDurationWithTimeout() = runTest {
        assertFailsWith<TimeoutCancellationException> { withTimeout(0L) {} }
        assertFailsWith<TimeoutCancellationException> { withTimeout(Duration.ZERO) {} }
    }

    @Test
    fun testZeroDurationWithTimeoutOrNull() = runTest {
        assertNull(withTimeoutOrNull(0L) {})
        assertNull(withTimeoutOrNull(Duration.ZERO) {})
    }
}
