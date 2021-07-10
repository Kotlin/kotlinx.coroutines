/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.time.*
import org.junit.Test
import java.lang.IllegalArgumentException
import java.util.concurrent.atomic.*
import kotlin.test.*
import kotlin.time.*

@OptIn(ExperimentalTime::class)
internal class TestNanoTimeSource : NanoTimeSource {
    @Volatile
    var nanos: Long = 0L
    override fun markNow(): NanoTimeMark = NanoTimeMark(nanos, this)
}

internal class Delayer {
    private val delayCounter = AtomicLong(0)
    fun delay(duration: Long) {
        delayCounter.addAndGet(duration)
    }

    fun getDelay(): Long = delayCounter.get()
    fun getDelayAndReset(): Long = delayCounter.getAndSet(0)
    fun reset(): Unit = delayCounter.set(0)
}

@OptIn(ExperimentalTime::class)
internal class NanoTimeMarkTest {

    private val timeSource = TestNanoTimeSource()
    private val nearEndOfTime = NanoTimeMark(Long.MAX_VALUE - 2, timeSource)
    private val nearStartOfTime = NanoTimeMark(Long.MIN_VALUE + 2, timeSource)
    private val justShortOfOneDay = Duration.days(1) - Duration.nanoseconds(1)

    @Test
    fun roll_over_max_test() {
        var mark = nearEndOfTime
        mark += Duration.nanoseconds(5)
        assertEquals(actual = mark.nanos, expected = Long.MIN_VALUE + 3)

        val mark2 = nearEndOfTime + justShortOfOneDay
        assertTrue(mark2.nanos < 0)
        assertTrue( mark2 > mark)
    }

    @Test
    fun roll_under_min_test() {
        var mark = nearStartOfTime
        mark -= Duration.nanoseconds(5)
        assertEquals(actual = mark.nanos, expected = Long.MAX_VALUE - 3)

        val mark2 = nearStartOfTime - justShortOfOneDay
        assertTrue(mark2.nanos > 0)
        assertTrue( mark2 < mark)
    }

    @Test
    fun compare_roll_over_test() {
        timeSource.nanos = Long.MAX_VALUE - 2
        val mark1 = timeSource.markNow()
        timeSource.nanos += 5
        val mark2 = timeSource.markNow()

        assertEquals(
            message = "Numeric roll over needs to have happened",
            expected = Long.MIN_VALUE + 2,
            actual = mark2.nanos
        )
        assertTrue(
            mark2 > mark1,
            message = "Rolled over time needs to be greater than previous value"
        )
    }

    @Test
    fun mid_value_compare() {
        timeSource.nanos = 0L
        val mark1 = timeSource.markNow()
        timeSource.nanos += 5
        val mark2 = timeSource.markNow()

        assertEquals(
            expected = 5L,
            actual = mark2.nanos
        )
        assertTrue(mark2 > mark1)
        assertTrue(mark1 < mark2)
    }

    @Test
    fun positive_and_negative_duration_from_extreme_subtract() {
        timeSource.nanos = Long.MAX_VALUE - 2
        val mark1 = timeSource.markNow()
        timeSource.nanos = Long.MIN_VALUE + 2
        val mark2 = timeSource.markNow()

        val diff1 = mark1 - mark2
        assertEquals(-5, diff1.inWholeNanoseconds)

        val diff2 = mark2 - mark1
        assertEquals(5, diff2.inWholeNanoseconds)
    }

    @Test
    fun comparing_different_time_sources(){
        val mark1 = timeSource.markNow()
        val timeSource2 = TestNanoTimeSource()
        val mark2 = timeSource2.markNow()

        assertFailsWith(IllegalArgumentException::class){
            mark1 > mark2
        }
        assertFailsWith(IllegalArgumentException::class){
            mark1 < mark2
        }
        assertFailsWith(IllegalArgumentException::class){
            mark1 - mark2
        }
        assertFailsWith(IllegalArgumentException::class){
            mark2 - mark1
        }
    }
}
