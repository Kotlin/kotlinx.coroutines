/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.sync

import kotlin.math.max
import kotlinx.coroutines.delay

/**
 * Limit throughput of events per second to be at most equal to the argument eventsPerSecond.
 * When the limit is passed, calls are suspended until the calculated point in time when it's
 * okay to pass the rate limiter.
 */
public interface RateLimiter {
    /**
     * Acquires a single permit from this RateLimiter, blocking until the request can be granted. Tells the amount of time slept, if any.
     */
    public abstract suspend fun acquire(): Long
    /**
     * Acquires the given number of permits from this RateLimiter, blocking until the request can be granted.
     */
    public abstract suspend fun acquire(permits: Int): Long
}

public fun rateLimiter(eventsPerSecond: Int):RateLimiter = RateLimiterImpl(eventsPerSecond)

internal class RateLimiterImpl(private val eventsPerSecond: Int) : RateLimiter {

    init {
        require(eventsPerSecond >= 1) {
            "At least one event per second is required"
        }
    }

    private val mutex = Mutex()
    private var next = 0L
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

    override suspend fun acquire(): Long {
        val delayMillis: Long = delaySequence.next()
        return acquireDelay(delayMillis)
    }

    override suspend fun acquire(permits: Int): Long {
        val delayMillis: Long = (1..permits).map { delaySequence.next() }.sum()
        return acquireDelay(delayMillis)
    }

    private suspend fun acquireDelay(delayMillis: Long): Long {
        val now: Long = System.currentTimeMillis()
        val until = mutex.withLock {
            max(next, now).also {
                next = it + delayMillis
            }
        }
        return if (until != now) {
            (until - now).also { sleep ->
                delay(sleep)
            }
        } else {
            0L
        }
    }
}
