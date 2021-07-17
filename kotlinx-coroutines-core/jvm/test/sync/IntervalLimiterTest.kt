/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import kotlin.test.*
import kotlin.time.*

@RunWith(Parameterized::class)
@ExperimentalTime
@ExperimentalThroughputLimiter
class IntervalLimiterParamTest(
    private val eventsPerInterval: Int
) {

    companion object {

        @JvmStatic
        @Parameterized.Parameters(name = "{0} events per interval")
        fun data(): Collection<Array<Int>> = listOf(1, 3, 10, 100, 1000).map { arrayOf(it) }
    }

    @Test
    internal fun run_for_several_intervals(): Unit = runBlocking {
        val timeSource = TestNanoTimeSource()
        val delayer = Delayer()
        val intervalLimiter: IntervalLimiter = IntervalLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = Duration.seconds(1),
            timeSource = timeSource,
            delay = delayer::delay
        )
        val laps = 10
        var pokes = 0
        (0 until eventsPerInterval * laps).forEach { idx ->
            pokes++
            delayer.reset()
            intervalLimiter.acquire()
            val delay: Long = (idx / eventsPerInterval) * 1000L
            assertEquals(
                expected = delay,
                actual = delayer.getDelay(),
                message = "Permit #${idx} for $eventsPerInterval events/interval should be delayed $delay ms"
            )
        }
        assertEquals(eventsPerInterval * laps, pokes, "The test is wrong, wrong number of iterations")
    }

    @Test
    internal fun try_acquire(): Unit = runBlocking {
        val timeSource = TestNanoTimeSource()
        val delayer = Delayer()
        val intervalLimiter: IntervalLimiter = IntervalLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = Duration.seconds(1),
            timeSource = timeSource,
            delay = delayer::delay
        )
        (1..eventsPerInterval).forEach {
            assertTrue(
                actual = intervalLimiter.tryAcquire(),
                message = "Permit #$it was supposed to be allowed"
            )
        }
        assertFalse(
            actual = intervalLimiter.tryAcquire(),
            message = "Permit #${eventsPerInterval + 1} was supposed to be disallowed"
        )
    }

    @Test
    internal fun try_acquire_on_stale_limiter(): Unit = runBlocking {
        val timeSource = TestNanoTimeSource()
        val delayer = Delayer()
        val interval = Duration.seconds(1)
        val intervalLimiter: IntervalLimiter = IntervalLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = interval,
            timeSource = timeSource,
            delay = delayer::delay
        )
        assertTrue(
            intervalLimiter.tryAcquire(eventsPerInterval * 2),
            message = "First permit should be granted"
        )

        timeSource.nanos += interval.inWholeNanoseconds * 3
        assertTrue(
            intervalLimiter.tryAcquire(eventsPerInterval),
            message = "Stale permit should be granted"
        )
        assertFalse(
            intervalLimiter.tryAcquire(),
            message = "Exhausted permit should not be granted"
        )
        assertEquals(
            expected = 0,
            actual = delayer.getDelay(),
            message = "Zero delay was expected"
        )
    }

    @Test
    internal fun warm_up_period_test(): Unit = runBlocking {
        val timeSource = TestNanoTimeSource()
        val delayer = Delayer()
        val interval = Duration.seconds(1)
        val intervalLimiter: IntervalLimiter = IntervalLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = interval,
            timeSource = timeSource,
            delay = delayer::delay,
            warmupPeriod = interval * 2
        )

        repeat(10) {
            assertTrue(
                intervalLimiter.tryAcquire(eventsPerInterval * 100),
                "Permits inside warmup period should be granted"
            )
        }
        timeSource.nanos = (interval * 2).inWholeNanoseconds
        assertTrue(intervalLimiter.tryAcquire(eventsPerInterval - 1), "Permit should be granted")
        assertTrue(intervalLimiter.tryAcquire(1), "Last permit before we move out of interval should be granted")
        assertFalse(intervalLimiter.tryAcquire(1), "First permit outside of interval should not be granted")
    }
}

@ExperimentalTime
@ExperimentalThroughputLimiter
internal class IntervalLimiterTest {

    private val timeSource = TestNanoTimeSource()
    private val delayer = Delayer()
    private val permits: Int = 100000
    private val interval = Duration.days(1) - Duration.nanoseconds(1)
    private val intervalMillis = interval.inWholeMilliseconds

    private val permitsPerInterval = 3
    private val limiter = IntervalLimiterImpl(
        eventsPerInterval = permitsPerInterval,
        interval = interval,
        timeSource = timeSource,
        delay = delayer::delay
    )

    @Test
    internal fun extreme_permits_number_tryAcquire(): Unit = runBlocking {
        assertFailsWith(IllegalArgumentException::class) {
            limiter.tryAcquire(permits)
        }
    }

    @Test
    internal fun extreme_permits_numbers_acquire(): Unit = runBlocking {
        assertFailsWith(IllegalArgumentException::class) {
            limiter.acquire(permits)
        }
    }

    @Test
    internal fun get_permits_at_the_end_of_time(): Unit = runBlocking {
        timeSource.nanos = Long.MAX_VALUE - 1

        // Take all permits for this interval, make time roll over into negative
        assertTrue(limiter.tryAcquire(permitsPerInterval))
        assertEquals(expected = 0L, actual = delayer.getDelay()) // No delay for the first taker

        // Take another permit
        assertTrue(limiter.tryAcquire())
        // This time we should be delayed
        assertTrue(delayer.getDelay() >= intervalMillis -1 && delayer.getDelay() <= intervalMillis + 1,
            message = "Delay of ${delayer.getDelay()} ms was recorded where ca $intervalMillis was expected.")
    }

    @Test
    internal fun test_max_permit_size(): Unit = runBlocking {
        assertFailsWith(IllegalArgumentException::class) {
            limiter.tryAcquire((permitsPerInterval * 10) + 1)
        }
        assertTrue(limiter.tryAcquire(permitsPerInterval * 10))
    }
}
