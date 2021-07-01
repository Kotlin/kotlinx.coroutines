/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import org.junit.Test
import kotlin.test.*
import kotlinx.coroutines.*

internal class ThroughputLimiterTest {

    private val testDelays = listOf(1, 10, 100, 1000, 1200, 1990, 100_000)

    @Test
    internal fun `delaySequence sum is 1000`() {
        val testResults = mutableListOf<Pair<Int, Long>>()
        testDelays.forEach { eventsPerSec ->
            val rateLimiter = RateLimiterImpl(eventsPerSec)
            val seq = rateLimiter.createDelaySequence()
            val delays = seq.take(eventsPerSec)
            val fullSecond = delays.sum()
            testResults.add(eventsPerSec to fullSecond)
        }
        testResults.forEach { (eventsPerSecond, fullRotationSum) ->
            assertEquals(fullRotationSum, 1000L, "$eventsPerSecond events per second should sum to 1000 ms delay, but was $fullRotationSum")
        }
    }

    @Test
    internal fun `some known delays`() {
        val testData = listOf<Pair<Int,Long>>(1 to 1000L, 1000 to 1L, 2 to 500L, 3 to 334L, 4 to 250L, 10_000 to 1L)
        testData.forEach { (eventsPerSecond: Int, delayTime: Long) ->
            val actual = RateLimiterImpl(eventsPerSecond).createDelaySequence().first()
            assertEquals(actual, delayTime, "Calculated delay time $actual didn't match expected $delayTime for $eventsPerSecond events per second")
        }
    }

    @Test(timeout = 2_000L)
    internal fun `run for one second`(): Unit = runBlocking {
        testDelays.map { eventsPerSec ->
            launch {
                val rateLimiter = rateLimiter(eventsPerSec)
                val start = System.currentTimeMillis()
                (0..eventsPerSec).forEach {
                    rateLimiter.acquire()
                }
                val end = System.currentTimeMillis()
                val diff = end - start
                assertTrue(diff > 999, "Suspended for too short time. Only $diff ms has passed and 1000 is expected. Ran at a rate of $eventsPerSec events per second.")
                assertTrue(diff < 1050, "Suspended for too long time. $diff ms has passed and at most 1050 is expected. Ran at a rate of $eventsPerSec events per second.")
            }
        }
    }
}
