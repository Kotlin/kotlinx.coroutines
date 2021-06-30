/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import java.util.concurrent.atomic.AtomicLong
import kotlinx.coroutines.delay

/**
 * Limit throughput of events per second to be at most equal to the argument eventsPerSecond.
 * When the limit is passed, calls are suspended until the calculated point in time when it's
 * okay to pass the rate limiter.
 */
public interface RateLimiter {
    public abstract suspend fun acquire()
}

public fun rateLimiter(eventsPerSecond: Int):RateLimiter = RateLimiterImpl(eventsPerSecond)

internal class RateLimiterImpl(private val eventsPerSecond: Int) : RateLimiter {

    init {
        require(eventsPerSecond >= 1) {
            "At least one event per second is required"
        }
    }

    private val last = AtomicLong()
    private val delaySequence: Iterator<Long> = createDelaySequence().iterator()

    /**
     * Generate an infinite sequence that will always sum to 1000 (millis)
     * for entries taken equal to eventsPerSecond<br>
     *
     * <code>
     * createDelaySequence().take(eventsPerSecond).sum() == 1000L
     * </code>
     */
    fun createDelaySequence(): Sequence<Long> {
        if (eventsPerSecond > 1000) {
            return generateSequence(0) { (it + 1) % eventsPerSecond }
                .map { if (it > 999) 0 else 1 }
        }
        val delayTimeBase: Long = (1000 / eventsPerSecond).toLong()
        val delayBonusTime = 1000 % eventsPerSecond
        return if (delayBonusTime == 0) {
            generateSequence { delayTimeBase }
        } else {
            generateSequence(0) { (it + 1) % eventsPerSecond }
                .map { if (it < delayBonusTime) delayTimeBase + 1 else delayTimeBase }
        }
    }

    /**
     * Suspend the current coroutine until it's calculated time of exit
     * from the rate limiter
     */
    override suspend fun acquire() {
        val now: Long = System.currentTimeMillis()
        val delay: Long = delaySequence.next()
        val until: Long = last.accumulateAndGet(now) { current, nowTime ->
            val currentPlus = current + delay
            if (currentPlus <= nowTime) {
                nowTime
            } else {
                currentPlus
            }
        }
        if (until != now) {
            delay(until - now)
        }
    }
}
