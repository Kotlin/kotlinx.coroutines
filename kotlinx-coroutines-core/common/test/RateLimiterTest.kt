/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import kotlinx.coroutines.rateLimiter.*
import kotlin.test.*
import kotlin.time.*

class RateLimiterTest : TestBase() {

    private fun zeroWait(limiter: RateLimitingAlgorithm, start: Long, refillPeriod: Long, tokens: Long): Long {
        val n = 10
        for (i in 1..n) {
            val time = start + refillPeriod * i
            val slot = limiter.requestTimeSlot(time, tokens, 0)
            assertTrue(slot <= time, "acquisition should not require waiting")
        }
        return start + refillPeriod * n
    }

    private fun fullWait(limiter: RateLimitingAlgorithm, start: Long, refillPeriod: Long, tokens: Long): Long {
        val slot = limiter.requestTimeSlot(start + refillPeriod, tokens, Long.MAX_VALUE)
        val n = 10
        for (i in 1..n) {
            val time = slot + refillPeriod * i
            assertEquals(time, limiter.requestTimeSlot(time, tokens, Long.MAX_VALUE))
        }
        return slot + refillPeriod * n
    }

    private fun exceedCapacity(limiter: RateLimitingAlgorithm, start: Long, refillPeriod: Long, tokens: Long): Long {
        val n = 10
        val k = 3
        for (i in 1..n) {
            val time = start + refillPeriod * k * i
            assertEquals(Long.MAX_VALUE,
                limiter.requestTimeSlot(time, tokens * k, refillPeriod * (k - 1) - 1))
            assertEquals(time + refillPeriod * (k - 1),
                limiter.requestTimeSlot(time, tokens * k, refillPeriod * (k - 1)))
        }
        return start + refillPeriod * k * (n + 1)
    }

    @Test
    fun tokenBucketTest() {
        val algo = TokenBucketRateLimiter(0,
            arrayOf(Bandwidth(3, 5, 2, 1)))
        val t1 = zeroWait(algo, 1, 5, 2)
        val t2 = fullWait(algo, t1, 5, 2)
        val t3 = exceedCapacity(algo, t2, 5, 2)
    }
}
