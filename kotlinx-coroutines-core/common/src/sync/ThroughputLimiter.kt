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
@OptIn(ExperimentalTime::class)
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
@OptIn(ExperimentalTime::class)
public interface IntervalLimiter : ThroughputLimiter

@SinceKotlin("1.5")
@OptIn(ExperimentalTime::class)
public fun intervalLimiter(eventsPerInterval: Int, interval: Duration): IntervalLimiter =
    IntervalLimiterImpl(eventsPerInterval, interval)

@SinceKotlin("1.5")
@OptIn(ExperimentalTime::class)
internal class IntervalLimiterImpl(
    eventsPerInterval: Int,
    interval: Duration,
    val timeSource: LongTimeSource = LongTimeSource(),
    val delay: suspend (Long) -> Unit = { kotlinx.coroutines.delay(it) }
) : IntervalLimiter {

    init {
        require(interval.inWholeMilliseconds > 5) {
            "Interval has to be at least 5 ms. The overhead of having locks and such in place if enough to render this moot."
        }
        require(interval.inWholeDays <= 1) {
            "Interval has to be less than 1 day"
        }
        require(interval.inWholeNanoseconds / eventsPerInterval > 1) {
            "Interval segment is not allowed to be less than one"
        }
    }

    private val _interval = Duration.nanoseconds(interval.inWholeNanoseconds)
    private val mutex = Mutex()
    private val eventSegment = _interval.div(eventsPerInterval)
    private val counter = ThroughputCounter(CoroutineScope(Dispatchers.Default))

    private var intervalStartCursor: LongTimeMark = timeSource.markNow()
    private var cursor: LongTimeMark = intervalStartCursor + eventSegment
    private var intervalEndCursor: LongTimeMark = intervalStartCursor + _interval

    override suspend fun acquire(): Long = acquire(permits = 1)
    override suspend fun acquire(permits: Int): Long {
        if (permits < 0) throw IllegalArgumentException("You need to ask for at least zero permits")

        val now: LongTimeMark = timeSource.markNow()
        val permitDuration = if (permits == 1) eventSegment else eventSegment.times(permits)

        val wakeUpTime: LongTimeMark = mutex.withLock {
            getWakeUpTime(now, permitDuration)
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
        if (permits < 0) throw IllegalArgumentException("You need to ask for at least zero permits")

        val now: LongTimeMark = timeSource.markNow()
        val timeoutEnd: LongTimeMark = if (timeout == null) now else now + timeout
        // Early elimination without waiting for locks
        if (!shouldAllowOnTry(now, timeoutEnd)) {
            // Start of current interval is in the future
            counter.count(DENIED, permits)
            return false
        }

        val permitDuration = if (permits == 1) eventSegment else eventSegment.times(permits)
        val wakeUpTime: LongTimeMark = mutex.withLock {
            // Late elimination with locks
            // In case things changed while waiting for the lock
            if (!shouldAllowOnTry(now, timeoutEnd)) {
                counter.count(DENIED, permits)
                return false
            }
            getWakeUpTime(now, permitDuration)
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
    private fun getWakeUpTime(now: LongTimeMark, permitDuration: Duration): LongTimeMark {
        return if (intervalEndCursor < now) {
            // Active interval is in the past
            // Align start of interval with current point in time
            intervalStartCursor = now
            intervalEndCursor = now + _interval
            cursor = intervalStartCursor + permitDuration
            // No delay
            // println("Settign up")
            now
        } else if (cursor > intervalEndCursor) {
            // Cursor has moved into new interval
            // Move cursors to match new interval
            val displacement = getDisplacement()
            intervalEndCursor += displacement
            intervalStartCursor += displacement
            cursor += permitDuration
            // println("Cursor beyond interval, moving interval $intervalSteps steps")
            intervalStartCursor
        } else if (intervalStartCursor > now) {
            // Active interval is in the future, and the current permit must be delayed
            cursor += permitDuration
            // println("Cursor in future interval")
            intervalStartCursor
        } else {
            // Now and Cursor are within the active interval
            // Only need to move the Cursor, nothing else
            // No delay
            cursor += permitDuration
            // println("Nothing special - cursor in first interval")
            now
        }
    }

    private fun getDisplacement(): Duration {
        val cursorDiff = cursor - intervalEndCursor
        var intervalSteps: Int = (cursorDiff.inWholeNanoseconds / _interval.inWholeNanoseconds).toInt()
        if (cursorDiff.inWholeNanoseconds % _interval.inWholeNanoseconds > 9) intervalSteps++
        return _interval.times(intervalSteps)
    }

    private fun shouldAllowOnTry(now: LongTimeMark, timeoutEnd: LongTimeMark): Boolean {
        return if (now > intervalEndCursor) {
            // println("Stale interval")
            return true
        } else if (cursor > intervalEndCursor) {
            val displacement: Duration = getDisplacement()
            val newStart: LongTimeMark = intervalStartCursor + displacement
            // println("Timeout end is going to be before the new start of period ${(timeoutEnd - newStart).inWholeNanoseconds}ns diff")
            return timeoutEnd >= newStart
        } else {
            // println("Cursor doesn't need mod to eval")
            timeoutEnd >= intervalStartCursor
        }
    }

    public override fun stats(): Map<ThroughputCounterEventType, Long> = counter.stats
    public override fun resetStats() = counter.reset()
}

/**
 * Limit throughput of events per second to be at most equal to the argument eventsPerInterval.
 * When the limit is passed, calls are suspended until the calculated point in time when it's
 * okay to pass the rate limiter.
 */
@SinceKotlin("1.5")
public interface RateLimiter : ThroughputLimiter

@SinceKotlin("1.5")
@OptIn(ExperimentalTime::class)
public fun rateLimiter(eventsPerInterval: Int, interval: Duration): RateLimiter =
    RateLimiterImpl(eventsPerInterval, interval)

@SinceKotlin("1.5")
@OptIn(ExperimentalTime::class)
internal class RateLimiterImpl(
    eventsPerInterval: Int,
    interval: Duration,
    val timeSource: LongTimeSource = LongTimeSource(),
    val delay: suspend (Long) -> Unit = { kotlinx.coroutines.delay(it) }
) : RateLimiter {

    private val mutex = Mutex()
    private val _interval = Duration.nanoseconds(interval.inWholeNanoseconds)
    private val permitDuration = _interval.div(eventsPerInterval)
    private val counter = ThroughputCounter(CoroutineScope(Dispatchers.Default))

    private var cursor: LongTimeMark = timeSource.markNow()

    init {
        require(interval.inWholeMilliseconds > 5) {
            "Interval has to be at least 5 ms. The overhead of having locks and such in place is enough to render this slow."
        }
        require(interval.inWholeDays <= 1) {
            "Interval has to be less than 1 day"
        }
    }

    override suspend fun acquire(): Long {
        return acquire(1)
    }

    override suspend fun acquire(permits: Int): Long {
        val permitDuration: Duration = if (permits == 1) permitDuration else permitDuration.times(permits)
        val now: LongTimeMark = timeSource.markNow()
        val wakeUpTime: LongTimeMark = mutex.withLock {
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
        val permitDuration: Duration = if (permits == 1) permitDuration else permitDuration.times(permits)
        val now: LongTimeMark = timeSource.markNow()
        val timeoutMark = if (timeout == null) now else now + timeout

        if (cursor > timeoutMark) {
            counter.count(DENIED, permits)
            return false
        }
        val wakeUpTime: LongTimeMark = mutex.withLock {
            val base = if (cursor > now) cursor else now
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
            for(msg in channel){
                if (msg.type == RESET){
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
