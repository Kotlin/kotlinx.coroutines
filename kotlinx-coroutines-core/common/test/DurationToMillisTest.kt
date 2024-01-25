package kotlinx.coroutines

import kotlin.test.*
import kotlin.time.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.nanoseconds
import kotlin.time.Duration.Companion.seconds

class DurationToMillisTest {

    @Test
    fun testNegativeDurationCoercedToZeroMillis() {
        assertEquals(0L, (-1).seconds.toDelayMillis())
    }

    @Test
    fun testZeroDurationCoercedToZeroMillis() {
        assertEquals(0L, 0.seconds.toDelayMillis())
    }

    @Test
    fun testOneNanosecondCoercedToOneMillisecond() {
        assertEquals(1L, 1.nanoseconds.toDelayMillis())
    }

    @Test
    fun testOneSecondCoercedTo1000Milliseconds() {
        assertEquals(1_000L, 1.seconds.toDelayMillis())
    }

    @Test
    fun testMixedComponentDurationRoundedUpToNextMillisecond() {
        assertEquals(999L, (998.milliseconds + 75909.nanoseconds).toDelayMillis())
    }

    @Test
    fun testOneExtraNanosecondRoundedUpToNextMillisecond() {
        assertEquals(999L, (998.milliseconds + 1.nanoseconds).toDelayMillis())
    }

    @Test
    fun testInfiniteDurationCoercedToLongMaxValue() {
        assertEquals(Long.MAX_VALUE, Duration.INFINITE.toDelayMillis())
    }

    @Test
    fun testNegativeInfiniteDurationCoercedToZero() {
        assertEquals(0L, (-Duration.INFINITE).toDelayMillis())
    }

    @Test
    fun testNanosecondOffByOneInfinityDoesNotOverflow() {
        assertEquals(Long.MAX_VALUE / 1_000_000, (Long.MAX_VALUE - 1L).nanoseconds.toDelayMillis())
    }

    @Test
    fun testMillisecondOffByOneInfinityDoesNotIncrement() {
        assertEquals((Long.MAX_VALUE / 2) - 1, ((Long.MAX_VALUE / 2) - 1).milliseconds.toDelayMillis())
    }

    @Test
    fun testOutOfBoundsNanosecondsButFiniteDoesNotIncrement() {
        val milliseconds = Long.MAX_VALUE / 10
        assertEquals(milliseconds, milliseconds.milliseconds.toDelayMillis())
    }
}
