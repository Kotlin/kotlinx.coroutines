/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import kotlinx.coroutines.rateLimiter.*
import kotlin.test.*
import kotlin.time.*

@ExperimentalTime
class RateLimiterTest : TestBase() {

    private fun zeroWait(limiter: RateLimiterImplBase, clock: Clock, refillPeriod: Long, tokens: Long) {
        val n = 10
        for (i in 1..n) {
            clock.advanceBy(refillPeriod)
            val time = clock.currentTimeNanos
            assertTrue(limiter.nextAvailableTime(time, tokens) <= time)
            val slot = limiter.requestTimeSlot(time, tokens, 0)
            assertEquals(slot + refillPeriod, limiter.nextAvailableTime(time + 1, tokens))
            assertTrue(slot <= time, "acquisition should not require waiting")
        }
    }

    private fun fullWait(limiter: RateLimiterImplBase, clock: Clock, refillPeriod: Long, tokens: Long) {
        clock.advanceBy(refillPeriod)
        val slot = limiter.requestTimeSlot(clock.currentTimeNanos, tokens * 3, Long.MAX_VALUE)
        clock.advanceTo(slot)
        val n = 10
        for (i in 0..n) {
            val time = clock.currentTimeNanos
            assertEquals(time + refillPeriod, limiter.nextAvailableTime(time, tokens))
            assertEquals(time + refillPeriod, limiter.requestTimeSlot(time + 1, tokens, Long.MAX_VALUE))
            assertEquals(time + refillPeriod * 2, limiter.nextAvailableTime(time + 2, tokens))
            clock.advanceBy(refillPeriod)
        }
    }

    private fun exceedCapacity(limiter: RateLimiterImplBase, clock: Clock, refillPeriod: Long, tokens: Long) {
        val n = 10
        val k = 3
        for (i in 1..n) {
            clock.advanceBy(refillPeriod * k)
            val time = clock.currentTimeNanos
            assertEquals(Long.MAX_VALUE,
                limiter.requestTimeSlot(time, tokens * k, refillPeriod * (k - 1) - 1))
            assertTrue(limiter.nextAvailableTime(time, tokens) <= time)
            for (v in 1 until k) {
                assertEquals(time + refillPeriod * v, limiter.nextAvailableTime(time, tokens * (v + 1)))
            }
            assertEquals(time + refillPeriod * (k - 1),
                limiter.requestTimeSlot(time, tokens * k, refillPeriod * (k - 1)))
        }
        clock.advanceBy(refillPeriod * k)
    }

    /** [RateLimiterImplBase.relinquishTokens] should never return enough tokens for an operation being possible
     * when another operation has just been issued. */
    private fun relinquishSmokeTest(limiter: RateLimiterImplBase, clock: Clock, refillPeriod: Long, tokens: Long) {
        val k = 30
        limiter.requestTimeSlot(clock.currentTimeNanos, tokens, 0)
        /** This reservation will be available at a moment X. */
        val hugeReservationTime = clock.currentTimeNanos
        val reservations = (1..k).map {
            limiter.requestTimeSlot(hugeReservationTime, tokens, refillPeriod * k).also {
                assertNotEquals(Long.MAX_VALUE, it)
            }
        }
        val hugeReservation = reservations[reservations.size - 1]
        /** After that huge reservation, no operations will be possible for at least [refillPeriod]. */
        assertEquals(Long.MAX_VALUE, limiter.requestTimeSlot(hugeReservation, tokens, refillPeriod - 1))
        val nextReservation = limiter.requestTimeSlot(hugeReservationTime + 1, tokens, Long.MAX_VALUE)
        assertEquals(hugeReservation + refillPeriod, nextReservation)
        /** Returning tokens should do nothing by this point: another reservation was made already, and if the rate
         * limiter gained any tokens at all, the limit could be broken. */
        reservations.map {
            limiter.relinquishTokens(hugeReservationTime + 2, it, tokens)
        }
        assertEquals(Long.MAX_VALUE, limiter.requestTimeSlot(nextReservation, tokens, 0))
    }

    @Test
    fun testTokenBucket() {
        val refillPeriod = 50L
        val quantum = 2L
        val algorithm = TokenBucketRateLimiter(arrayOf(Bandwidth(3, refillPeriod, quantum, 1)))
        val clock = Clock(algorithm.timeSinceInitialization())
        zeroWait(algorithm, clock, refillPeriod, quantum)
        fullWait(algorithm, clock, refillPeriod, quantum)
        exceedCapacity(algorithm, clock, refillPeriod, quantum)
        relinquishSmokeTest(algorithm, clock, refillPeriod, quantum)
    }
}

private class Clock(var currentTimeNanos: Long) {
    fun advanceBy(nanos: Long) {
        currentTimeNanos += nanos
    }

    fun advanceTo(timeNanos: Long) {
        require(timeNanos >= currentTimeNanos)
        currentTimeNanos = timeNanos
    }
}
