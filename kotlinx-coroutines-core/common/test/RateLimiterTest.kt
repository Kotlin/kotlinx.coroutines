/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import kotlinx.coroutines.rateLimiter.*
import kotlin.test.*
import kotlin.time.*

@ExperimentalTime
class RateLimiterTest : TestBase() {

    private fun zeroWait(limiter: RateLimiterImplBase, start: Long, refillPeriod: Long, tokens: Long): Long {
        val n = 10
        for (i in 1..n) {
            val time = start + refillPeriod * i
            assertTrue(limiter.nextAvailableTime(time, tokens) <= time)
            val slot = limiter.requestTimeSlot(time, tokens, 0)
            assertEquals(slot + refillPeriod, limiter.nextAvailableTime(time + 1, tokens))
            assertTrue(slot <= time, "acquisition should not require waiting")
        }
        return start + refillPeriod * n
    }

    private fun fullWait(limiter: RateLimiterImplBase, start: Long, refillPeriod: Long, tokens: Long): Long {
        val slot = limiter.requestTimeSlot(start + refillPeriod, tokens, Long.MAX_VALUE)
        val n = 10
        for (i in 0..n) {
            val time = slot + refillPeriod * i
            assertEquals(time + refillPeriod, limiter.nextAvailableTime(time, tokens))
            assertEquals(time + refillPeriod, limiter.requestTimeSlot(time + 1, tokens, Long.MAX_VALUE))
            assertEquals(time + refillPeriod * 2, limiter.nextAvailableTime(time + 2, tokens))
        }
        return slot + refillPeriod * (n + 1)
    }

    private fun exceedCapacity(limiter: RateLimiterImplBase, start: Long, refillPeriod: Long, tokens: Long): Long {
        val n = 10
        val k = 3
        for (i in 1..n) {
            val time = start + refillPeriod * k * i
            assertEquals(Long.MAX_VALUE,
                limiter.requestTimeSlot(time, tokens * k, refillPeriod * (k - 1) - 1))
            assertTrue(limiter.nextAvailableTime(time, tokens) <= time)
            for (v in 1 until k) {
                assertEquals(time + refillPeriod * v, limiter.nextAvailableTime(time, tokens * (v + 1)))
            }
            assertEquals(time + refillPeriod * (k - 1),
                limiter.requestTimeSlot(time, tokens * k, refillPeriod * (k - 1)))
        }
        return start + refillPeriod * k * (n + 1)
    }

    @Test
    fun tokenBucketTest() {
        val algo = TokenBucketRateLimiter(arrayOf(Bandwidth(3, 5, 2, 1)))
        val t0 = algo.timeSinceInitialization()
        val t1 = zeroWait(algo, t0, 5, 2)
        val t2 = fullWait(algo, t1, 5, 2)
        val t3 = exceedCapacity(algo, t2, 5, 2)
    }
}
