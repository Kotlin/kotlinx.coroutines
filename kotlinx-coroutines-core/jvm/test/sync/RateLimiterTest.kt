/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import kotlinx.coroutines.time.*
import org.junit.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import org.junit.runners.Parameterized.*
import kotlin.math.*
import kotlin.test.*
import kotlin.time.*

@RunWith(Parameterized::class)
@ExperimentalTime
@ExperimentalThroughputLimiter
internal class RateLimiterParamTest(private val eventsPerInterval: Int) {

    companion object {

        @JvmStatic
        @Parameters(name = "{0} events per interval")
        fun data(): Collection<Array<Int>> = listOf(1, 3, 10, 100, 1000).map { arrayOf(it) }
    }

    @Test
    internal fun acquire(): Unit = runBlocking {
        val delayer = Delayer()
        val timeSource: NanoTimeSource = TestNanoTimeSource()
        val rateLimiter = RateLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = Duration.seconds(1),
            timeSource = timeSource,
            delay = delayer::delay
        )
        (0..eventsPerInterval).forEach { delayMultiplier ->
            delayer.reset()
            val actualDelay = rateLimiter.acquire()
            val delaySum = delayer.getDelay()
            val expectedDelay: Long = (1000L / eventsPerInterval) * delayMultiplier
            assertEquals(
                expected = expectedDelay,
                actual = actualDelay,
                message = "Returned sleep time should be $expectedDelay ms"
            )
            assertEquals(
                expected = expectedDelay,
                actual = delaySum,
                message = "Failed for eventsPerInterval: $eventsPerInterval round #$delayMultiplier took $delaySum ms"
            )
        }
    }

    @Test
    internal fun try_acquire_one_less_with_timout(): Unit = runBlocking {
        val delayer = Delayer()
        val timeSource: NanoTimeSource = TestNanoTimeSource()
        val interval = Duration.seconds(10)
        val rateLimiter = RateLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = interval,
            timeSource = timeSource,
            delay = delayer::delay
        )
        delayer.reset()

        val permits = max(eventsPerInterval - 1, 1)
        assertTrue(
            rateLimiter.tryAcquire(permits, Duration.ZERO),
            message = "First permit should be granted"
        )
        assertTrue(
            rateLimiter.tryAcquire(interval),
            message = "Second permit should be granted"
        )
        assertFalse(
            rateLimiter.tryAcquire(),
            message = "Third permit should not be granted"
        )

        val permitSize = interval / eventsPerInterval
        val delayDuration = permitSize * permits
        val expectedDelayMillis = delayDuration.inWholeMilliseconds
        val actualDelayMillis = delayer.getDelay()
        Assert.assertEquals(
            "Unexpected delay for $eventsPerInterval events/interval",
            expectedDelayMillis,
            actualDelayMillis
        )
    }

    @Test
    internal fun try_acquire_one_less_without_timout(): Unit = runBlocking {
        val delayer = Delayer()
        val timeSource: NanoTimeSource = TestNanoTimeSource()
        val interval = Duration.seconds(10)
        val rateLimiter = RateLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = interval,
            timeSource = timeSource,
            delay = delayer::delay
        )
        delayer.reset()

        val permits: Int = max(eventsPerInterval - 1, 1)
        assertTrue(
            rateLimiter.tryAcquire(permits),
            message = "First permit should be granted"
        )
        assertFalse(
            rateLimiter.tryAcquire(),
            message = "Second permit should not be granted"
        )
    }

    @Test
    internal fun warm_up_period_tryAcquire_test(): Unit = runBlocking {
        val delayer = Delayer()
        val timeSource = TestNanoTimeSource()
        val interval = Duration.seconds(10)
        val rateLimiter = RateLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = interval,
            timeSource = timeSource,
            delay = delayer::delay,
            warmupPeriod = interval
        )
        repeat(10) {
            assertTrue(rateLimiter.tryAcquire(eventsPerInterval * 10))
        }

        timeSource.nanos += interval.inWholeNanoseconds - 1
        assertTrue(rateLimiter.tryAcquire(), "Still in warmup, should not be delayed")
        timeSource.nanos += 1
        assertTrue(rateLimiter.tryAcquire(eventsPerInterval), "First event out of warmup should not be delayed")

        assertEquals(
            expected = 0L,
            actual = delayer.getDelay(),
            message = "No delay should have been recorded so far, due to warm up period"
        )

        assertFalse(rateLimiter.tryAcquire(eventsPerInterval))
        assertTrue(rateLimiter.tryAcquire(eventsPerInterval, interval))
        val delayMillis =
            ((interval / eventsPerInterval) * eventsPerInterval).inWholeMilliseconds // Avoid fraction deviation
        assertEquals(delayMillis, delayer.getDelay())
    }

    @Test
    internal fun warm_up_period_acquire_test(): Unit = runBlocking {
        val delayer = Delayer()
        val timeSource = TestNanoTimeSource()
        val interval = Duration.seconds(10)
        val rateLimiter = RateLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = interval,
            timeSource = timeSource,
            delay = delayer::delay,
            warmupPeriod = interval
        )
        repeat(10) {
            assertEquals(0, rateLimiter.acquire(eventsPerInterval * 10))
        }

        timeSource.nanos += interval.inWholeNanoseconds - 1
        assertEquals(0, rateLimiter.acquire(), "Still in warmup, should not be delayed")
        timeSource.nanos += 1
        assertEquals(0, rateLimiter.acquire(eventsPerInterval), "First event out of warmup should not be delayed")

        assertEquals(
            expected = 0L,
            actual = delayer.getDelay(),
            message = "No delay should have been recorded so far, due to warm up period"
        )

        val delayMillis =
            ((interval / eventsPerInterval) * eventsPerInterval).inWholeMilliseconds // Avoid fraction deviation
        assertEquals(delayMillis, rateLimiter.acquire(eventsPerInterval))
        assertEquals(delayMillis, delayer.getDelay())
    }
}

@ExperimentalTime
@ExperimentalThroughputLimiter
internal class RateLimiterTest {

    private val timesource: TestNanoTimeSource = TestNanoTimeSource()
    private val delayer = Delayer()

    @Test
    internal fun get_permits_at_the_end_of_time():Unit = runBlocking {
        val interval = Duration.milliseconds(10)
        val limiter = RateLimiterImpl(
            eventsPerInterval = 1,
            interval = interval,
            timeSource = timesource,
            delay = delayer::delay,
            warmupPeriod = interval
        )
        timesource.nanos = Long.MAX_VALUE-2

        limiter.acquire()
        assertEquals(0L, delayer.getDelay())
        limiter.acquire()
        assertEquals(10L, delayer.getDelayAndReset())
        limiter.acquire()
        assertEquals(20L, delayer.getDelay())
    }

    @Test
    internal fun test_max_permit_size():Unit = runBlocking {
        val interval = Duration.days(1)
        val limiter = RateLimiterImpl(
            eventsPerInterval = 1,
            interval = interval,
            timeSource = timesource,
            delay = delayer::delay,
            warmupPeriod = interval
        )

        assertFailsWith(IllegalArgumentException::class) {
            limiter.tryAcquire(11)
        }
        assertTrue(limiter.tryAcquire(10))
    }
}
