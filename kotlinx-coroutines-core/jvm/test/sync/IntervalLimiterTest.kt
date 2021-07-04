/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync


import kotlin.test.*
import kotlin.time.*
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.test.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*

@RunWith(Parameterized::class)
@OptIn(ExperimentalTime::class)
class IntervalLimiterTest(
    private val eventsPerInterval: Int
) {

    companion object {

        @JvmStatic
        @Parameterized.Parameters(name = "{0} events per interval")
        fun data(): Collection<Array<Any>> = listOf(1, 3, 10, 100, 1000).map { arrayOf(it) }
    }

    @Test
    fun run_for_several_intervals(): Unit = runBlocking {
        val timeSource = TestLongTimeSource()
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
                delay,
                delayer.getDelay(),
                "Permit #${idx} for $eventsPerInterval events/interval should be delayed $delay ms"
            )
        }
        assertEquals(eventsPerInterval * laps, pokes, "The test is wrong, wrong number of iterations")
    }

    @Test
    fun try_acquire(): Unit = runBlocking {
        val timeSource = TestLongTimeSource()
        val delayer = Delayer()
        val intervalLimiter: IntervalLimiter = IntervalLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = Duration.seconds(1),
            timeSource = timeSource,
            delay = delayer::delay
        )
        (1..eventsPerInterval).forEach {
            assertTrue(intervalLimiter.tryAcquire(), "Permit #$it was supposed to be allowed")
        }
        assertFalse(intervalLimiter.tryAcquire(), "Permit #${eventsPerInterval + 1} was supposed to be disallowed")
    }

    @Test
    fun try_acquire_on_stale_limiter(): Unit = runBlocking {
        val timeSource = TestLongTimeSource()
        val delayer = Delayer()
        val interval = Duration.seconds(1)
        val intervalLimiter: IntervalLimiter = IntervalLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = interval,
            timeSource = timeSource,
            delay = delayer::delay
        )
        assertTrue(intervalLimiter.tryAcquire(eventsPerInterval))

        timeSource.nanos += interval.inWholeNanoseconds
        assertTrue(intervalLimiter.tryAcquire(eventsPerInterval))
    }
}
