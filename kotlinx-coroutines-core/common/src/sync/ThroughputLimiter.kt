/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.sync

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.sync.ThroughputCounterEventType.*
import kotlinx.coroutines.time.*
import kotlin.time.*

@SinceKotlin("1.5")
@ExperimentalTime
@ExperimentalThroughputLimiter
public interface ThroughputLimiter {
    /**
     * Acquires a single permit, blocking until the request can be granted. Tells the amount of time slept, if any.
     */
    public suspend fun acquire(): Long

    /**
     * Acquires the given number of permits, blocking until the request can be granted.
     */
    public suspend fun acquire(permits: Int): Long

    /**
     * Acquires a permit if it can be acquired immediately without delay.
     */
    public suspend fun tryAcquire(): Boolean

    /**
     * Acquires permits if it can be acquired immediately without delay.
     */
    public suspend fun tryAcquire(permits: Int): Boolean

    /**
     * Acquires the given number of permits if it can be obtained without exceeding the specified timeout, or returns false immediately (without waiting) if the permits would not have been granted before the timeout expired.
     */
    public suspend fun tryAcquire(permits: Int, timeout: Duration): Boolean

    /**
     * Acquires a permit if it can be obtained without exceeding the specified timeout, or returns false immediately (without waiting) if the permit would not have been granted before the timeout expired.
     */
    public suspend fun tryAcquire(timeout: Duration): Boolean

    /**
     * Get counts of permit resolutions, granted, denied and such.
     * @see ThroughputCounterEventType
     */
    public fun stats(): Map<ThroughputCounterEventType, Long>
    public fun resetStats()
}

/**
 * Limit throughput of events, per interval, to be at most equal to the argument eventsPerInterval.
 * When the limit is passed, calls are suspended until the calculated point in time when it's
 * okay to pass the rate limiter.
 */
@SinceKotlin("1.5")
@ExperimentalTime
@ExperimentalThroughputLimiter
public interface IntervalLimiter : ThroughputLimiter

/**
 * Limit throughput of events, per interval, to be at most equal to the argument eventsPerInterval.
 * When the limit is passed, calls are suspended until the calculated point in time when it's
 * okay to pass the rate limiter.
 */
@SinceKotlin("1.5")
@ExperimentalTime
@ExperimentalThroughputLimiter
public fun intervalLimiter(
    eventsPerInterval: Int,
    interval: Duration,
    warmupPeriod: Duration? = null
): IntervalLimiter =
    IntervalLimiterImpl(eventsPerInterval = eventsPerInterval, interval = interval, warmupPeriod = warmupPeriod)

@SinceKotlin("1.5")
@ExperimentalTime
@ExperimentalThroughputLimiter
internal class IntervalLimiterImpl(
    private val eventsPerInterval: Int,
    private val interval: Duration = Duration.seconds(1),
    private val timeSource: NanoTimeSource = NanoTimeSourceImpl,
    private val delay: suspend (Long) -> Unit = ::delay,
    warmupPeriod: Duration? = null
) : IntervalLimiter {

    init {
        require(interval.inWholeMilliseconds > 5) {
            "Interval has to be at least 5 ms. The overhead of having locks and such in place is enough to render this moot."
        }
        require(interval.inWholeDays <= 1) {
            "Interval has to be less than 1 day"
        }
        require(interval.inWholeNanoseconds / eventsPerInterval > 1) {
            "Interval segment is not allowed to be less than one"
        }
        require(warmupPeriod?.let { interval <= warmupPeriod } != false) {
            "Interval has to be greater or equal to the warmup period"
        }
        require(interval.inWholeNanoseconds != Long.MAX_VALUE) {
            "Interval overflowed"
        }
    }
    private val maxPermitDuration = Duration.days(10)
    private val maxPermits:Long = (maxPermitDuration / (interval / eventsPerInterval)).toLong()

    private var warmupMark: NanoTimeMark? = warmupPeriod?.let { timeSource.markNow() + it }
    private val mutex = Mutex()
    private val counter = ThroughputCounter(CoroutineScope(Dispatchers.Default))

    // Mutable state, access through mutex
    private var cursor: Long = 0
    private var intervalStartCursor: NanoTimeMark = timeSource.markNow()
    private var intervalEndCursor: NanoTimeMark = intervalStartCursor + interval
    // End Mutable state

    override suspend fun acquire(): Long = acquire(permits = 1)
    override suspend fun acquire(permits: Int): Long {
        if(permits < 0) throw IllegalArgumentException("Permits must be zero or larger")
        if(permits > maxPermits) throw IllegalArgumentException("You are not allowed to take $permits permits, max $maxPermits is allowed")

        val now: NanoTimeMark = timeSource.markNow()
        val wakeUpTime: NanoTimeMark = mutex.withLock {
            getWakeUpTime(now, permits)
        }
        val sleep: Duration = (wakeUpTime.minus(now))
        val sleepMillis = sleep.inWholeMilliseconds
        if (sleepMillis > 0) {
            counter.count(GRANTED_DELAYED, permits)
            delay(sleepMillis)
        } else {
            counter.count(GRANTED_IMMEDIATE, permits)
        }
        return sleepMillis
    }

    override suspend fun tryAcquire(): Boolean = tryAcquireInternal()
    override suspend fun tryAcquire(permits: Int): Boolean = tryAcquireInternal(permits = permits)
    override suspend fun tryAcquire(permits: Int, timeout: Duration): Boolean =
        tryAcquireInternal(permits = permits, timeout = timeout)

    override suspend fun tryAcquire(timeout: Duration): Boolean = tryAcquireInternal(timeout = timeout)
    private suspend fun tryAcquireInternal(permits: Int = 1, timeout: Duration? = null): Boolean {
        if(permits < 0) throw IllegalArgumentException("Permits must be zero or larger")
        if(permits > maxPermits) throw IllegalArgumentException("You are not allowed to take $permits permits, max $maxPermits is allowed")

        val now: NanoTimeMark = timeSource.markNow()
        val timeoutEnd: NanoTimeMark = if (timeout == null) now else now + timeout

        // Early elimination without waiting for locks
        if (!shouldAllowOnTry(now, timeoutEnd)) {
            // Start of current interval is in the future
            counter.count(DENIED, permits)
            return false
        }

        val wakeUpTime: NanoTimeMark = mutex.withLock {
            // Late elimination with locks
            // In case things changed while waiting for the lock
            if (!shouldAllowOnTry(now, timeoutEnd)) {
                counter.count(DENIED, permits)
                return false
            }
            getWakeUpTime(now, permits)
        }
        val sleep: Duration = (wakeUpTime.minus(now))
        val sleepMillis = sleep.inWholeMilliseconds
        if (sleepMillis > 0) {
            counter.count(GRANTED_DELAYED, permits)
            delay(sleepMillis)
        } else {
            counter.count(GRANTED_IMMEDIATE, permits)
        }
        return true
    }

    /**
     * Must be run inside the mutex.. This is the Danger Zone.
     */
    private fun getWakeUpTime(now: NanoTimeMark, permits: Int): NanoTimeMark {
        return if (warmupMark != null) {
            if (now < warmupMark!!) {
                now
            } else {
                warmupMark = null
                cursor = permits.toLong()
                intervalStartCursor = now
                intervalEndCursor = intervalStartCursor + interval
                now
            }
        } else if (intervalEndCursor < now) {
            // Active interval is in the past
            // Align start of interval with current point in time
            intervalStartCursor = now
            intervalEndCursor = intervalStartCursor + interval
            cursor = permits.toLong()
            // No delay
            // println("Setting up")
            now
        } else if (cursor >= eventsPerInterval) {
            // Cursor has moved into new interval
            // Move cursors to match new interval
            val displacement = getDisplacement()
            intervalEndCursor += displacement
            intervalStartCursor += displacement
            cursor = (cursor % eventsPerInterval) + permits
            // println("Cursor beyond interval, moving interval $intervalSteps steps")
            intervalStartCursor
        } else if (intervalStartCursor > now) {
            // Active interval is in the future, and the current permit must be delayed
            cursor += permits
            // println("Cursor in future interval")
            intervalStartCursor
        } else {
            // Now and Cursor are within the active interval
            // Only need to move the Cursor, nothing else
            // No delay
            cursor += permits
            // println("Nothing special - cursor in first interval")
            now
        }
    }

    private fun getDisplacement(): Duration {
        val intervalSteps: Int = (cursor / eventsPerInterval).toInt()
        return interval.times(intervalSteps)
    }

    private fun shouldAllowOnTry(now: NanoTimeMark, timeoutEnd: NanoTimeMark): Boolean {
        return if (warmupMark != null && warmupMark!! < now) {
            return true
        } else if (cursor >= eventsPerInterval) {
            val displacement: Duration = getDisplacement()
            val newStart: NanoTimeMark = intervalStartCursor + displacement
            // println("Timeout end is going to be before the new start of period ${(timeoutEnd - newStart).inWholeNanoseconds}ns diff")
            return timeoutEnd >= newStart
        } else if (now > intervalEndCursor) {
            // println("Stale interval")
            return true
        } else {
            // println("Cursor doesn't need mod to eval")
            timeoutEnd >= intervalStartCursor
        }
    }

    override fun stats(): Map<ThroughputCounterEventType, Long> = counter.stats
    override fun resetStats() = counter.reset()
}

/**
 * Limit throughput of events per interval to be at most equal to the argument eventsPerInterval.
 * When the limit is passed, calls are suspended until the calculated point in time when it's
 * okay to pass the rate limiter.
 */
@SinceKotlin("1.5")
@ExperimentalTime
@ExperimentalThroughputLimiter
public interface RateLimiter : ThroughputLimiter

/**
 * Limit throughput of events per interval to be at most equal to the argument eventsPerInterval.
 * When the limit is passed, calls are suspended until the calculated point in time when it's
 * okay to pass the rate limiter.
 */
@SinceKotlin("1.5")
@ExperimentalTime
@ExperimentalThroughputLimiter
public fun rateLimiter(eventsPerInterval: Int, interval: Duration, warmupPeriod: Duration? = null): RateLimiter =
    RateLimiterImpl(eventsPerInterval = eventsPerInterval, interval = interval, warmupPeriod = warmupPeriod)

@SinceKotlin("1.5")
@ExperimentalTime
@ExperimentalThroughputLimiter
internal class RateLimiterImpl(
    eventsPerInterval: Int,
    interval: Duration,
    private val timeSource: NanoTimeSource = NanoTimeSourceImpl,
    private val delay: suspend (Long) -> Unit = ::delay,
    warmupPeriod: Duration? = null,
) : RateLimiter {

    private val mutex = Mutex()
    private val permitDuration = interval.div(eventsPerInterval).round()
    private val counter = ThroughputCounter(CoroutineScope(Dispatchers.Default))

    private var warmupMark: NanoTimeMark? = warmupPeriod?.let { timeSource.markNow() + it }
    private var cursor: NanoTimeMark = timeSource.markNow()

    init {
        require(interval.inWholeMilliseconds > 5) {
            "Interval has to be at least 5 ms. The overhead of having locks and such in place is enough to render this slow."
        }
        require(interval.inWholeDays <= 1) {
            "Interval has to be less than 1 day"
        }
    }

    private val maxPermitDuration:Duration = Duration.days(10)
    private val maxPermits:Long = (maxPermitDuration / (interval / eventsPerInterval)).toLong()

    override suspend fun acquire(): Long {
        return acquire(1)
    }

    override suspend fun acquire(permits: Int): Long {
        if(permits < 0) throw IllegalArgumentException("Permits must be zero or larger")
        if(permits > maxPermits) throw IllegalArgumentException("You are not allowed to take $permits permits, max $maxPermits is allowed")

        val permitDuration: Duration = if (permits == 1) permitDuration else permitDuration.times(permits)
        val now: NanoTimeMark = timeSource.markNow()
        if (warmupMark?.let { it > now } == true) return 0L

        val wakeUpTime: NanoTimeMark = mutex.withLock {
            if (warmupMark != null) {
                warmupMark = null
                cursor = now
            }
            val base = if (cursor > now) cursor else now
            cursor = base + permitDuration
            base
        }
        val delayInMillis = (wakeUpTime - now).inWholeMilliseconds
        val countType: ThroughputCounterEventType = if (delayInMillis > 0) GRANTED_DELAYED else GRANTED_IMMEDIATE
        counter.count(countType, permits)
        delay(delayInMillis)
        return delayInMillis
    }

    override suspend fun tryAcquire(): Boolean = tryAcquire(1)
    override suspend fun tryAcquire(permits: Int): Boolean = tryAcquireInternal(permits, null)
    override suspend fun tryAcquire(permits: Int, timeout: Duration): Boolean = tryAcquireInternal(permits, timeout)
    override suspend fun tryAcquire(timeout: Duration): Boolean = tryAcquireInternal(1, timeout)

    private suspend fun tryAcquireInternal(permits: Int, timeout: Duration?): Boolean {
        if(permits < 0) throw IllegalArgumentException("Permits must be zero or larger")
        if(permits > maxPermits) throw IllegalArgumentException("You are not allowed to take $permits permits, max $maxPermits is allowed")

        val permitDuration: Duration = if (permits == 1) permitDuration else permitDuration.times(permits)
        val now: NanoTimeMark = timeSource.markNow()
        if (warmupMark?.let { it > now } == true) return true
        val timeoutMark = if (timeout == null) now else now + timeout

        if (warmupMark == null && cursor > timeoutMark) {
            counter.count(DENIED, permits)
            return false
        }
        val wakeUpTime: NanoTimeMark = mutex.withLock {
            val base = if (warmupMark != null) {
                warmupMark = null
                now
            } else if (cursor > now) {
                cursor
            } else {
                now
            }
            if (base > timeoutMark) {
                counter.count(DENIED, permits)
                return false
            }
            cursor = base + permitDuration
            base
        }
        val delayInMillis = (wakeUpTime - now).inWholeMilliseconds
        val countType: ThroughputCounterEventType = if (delayInMillis > 0) GRANTED_DELAYED else GRANTED_IMMEDIATE
        counter.count(countType, permits)
        delay(delayInMillis)
        return true
    }

    public override fun stats(): Map<ThroughputCounterEventType, Long> = counter.stats
    public override fun resetStats() = counter.reset()
}

private class ThroughputCounter(scope: CoroutineScope) {
    private val counter: MutableMap<ThroughputCounterEventType, Long> = mutableMapOf()
    private val channel = Channel<ThroughputCounterMessage>()

    init {
        scope.launch {
            for (msg in channel) {
                if (msg.type == RESET) {
                    counter.clear()
                } else {
                    counter[msg.type] = (counter[msg.type] ?: 0L) + 1
                }
            }
        }
    }

    internal suspend fun count(type: ThroughputCounterEventType, permits: Int) {
        channel.send(ThroughputCounterMessage(type, permits))
    }

    internal val stats: Map<ThroughputCounterEventType, Long> get() = HashMap(counter)
    internal fun reset() {
        counter.clear()
    }
}

@SinceKotlin("1.5")
public data class ThroughputCounterMessage(
    val type: ThroughputCounterEventType,
    val permits: Int
)

@SinceKotlin("1.5")
public enum class ThroughputCounterEventType {
    GRANTED_IMMEDIATE,
    GRANTED_DELAYED,
    DENIED,
    RESET,
}

@ExperimentalTime
internal fun Duration.round(): Duration {
    return when {
        this.inWholeMilliseconds == Long.MAX_VALUE -> throw IllegalArgumentException("Duration size overflow")
        this > Duration.days(100) -> throw IllegalArgumentException("We dont accept durations greater than 100 days for interval length or permits")
        this > Duration.days(1) -> Duration.minutes(this.inWholeMinutes)
        this > Duration.hours(1) -> Duration.seconds(this.inWholeSeconds)
        this > Duration.minutes(1) -> Duration.seconds(this.inWholeMilliseconds)
        else -> this
    }
}

//private operator fun Long.plus(other: Int):Long = this + other.toLong()
