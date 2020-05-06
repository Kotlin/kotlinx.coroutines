/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.flow.*
import kotlin.math.*
import kotlin.time.*

public abstract class RateLimiter {
    protected abstract fun requestTimeSlot(atTime: Long, tokens: Long, maxDelay: Long): Long
    protected abstract fun relinquishTokens(atTime: Long, takenAtTime: Long, tokens: Long)
    protected abstract fun addTokens(atTime: Long, tokens: Long)

    private suspend fun consume(tokens: Long, maxDelay: Long) {
        require(tokens > 0)
        val currentTime = nanoTime()
        val nextSlot = requestTimeSlot(currentTime, tokens, maxDelay)
        if (nextSlot == Long.MAX_VALUE) {
            throw UnsupportedOperationException("Could not allocate $tokens tokens to be available in $maxDelay")
        }
        val toSleep = nextSlot - currentTime
        try {
            delay(toSleep)
        } catch (e: CancellationException) {
            relinquishTokens(nanoTime(), currentTime, tokens)
        }
    }

    public fun addTokens(tokens: Long): Unit = addTokens(nanoTime(), tokens)
    public fun consumeTokens(tokens: Long): Unit = addTokens(-tokens)

    public fun tryConsume(tokens: Long = 1): Boolean {
        require(tokens > 0)
        return requestTimeSlot(nanoTime(), tokens, 0) != Long.MAX_VALUE
    }

    public suspend fun consume(tokens: Long = 1): Unit =
        consume(tokens, Long.MAX_VALUE)

    @ExperimentalTime
    public suspend fun consume(tokens: Long, maxDelay: Duration): Unit =
        consume(tokens, maxDelay.toLongNanoseconds())
}

internal class RateLimitedFlow<T>(
    val flow: Flow<T>, private val rateLimiter: RateLimiter, private val tokensPerValue: (T) -> Long): Flow<T> {
    @InternalCoroutinesApi
    override suspend fun collect(collector: FlowCollector<T>) {
        flow.collect {
            rateLimiter.consume(tokensPerValue(it))
            collector.emit(it)
        }
    }
}

public fun <T> Flow<T>.rateLimit(rateLimiter: RateLimiter, tokensPerValue: (T) -> Long): Flow<T> =
    RateLimitedFlow(this, rateLimiter, tokensPerValue)

internal data class Bandwidth(
    val capacity: Long, val refillPeriod: Long, val quantum: Long = 1, val initialAmount: Long = capacity) {
    init {
        require(capacity > 0)
        require(refillPeriod > 0)
        require(quantum > 0)
        require(initialAmount >= 0)
    }
}

internal class TokenBucketRateLimiter(bandwidths: Array<Bandwidth>): RateLimiter() {

    internal class State(internal val bandwidths: Array<Bandwidth>,
                         private val tokensPerBandwidth: Array<Long> =
                             Array(bandwidths.size) { bandwidths[it].initialAmount },
                         private val lastUpdateTimes: Array<Long> = run {
                             val currentTime = nanoTime()
                             Array(bandwidths.size) { currentTime }
                         },
                         var lastEventTime: Long = nanoTime())
    {
        init { require(bandwidths.isNotEmpty()) }

        fun copyOf(): State = State(bandwidths, tokensPerBandwidth.copyOf(), lastUpdateTimes.copyOf(), lastEventTime)

        val availableTokens get() = tokensPerBandwidth.reduce { a, b -> min(a, b) }

        fun refill(atTime: Long) {
            for (i in 0..bandwidths.size) {
                val bandwidth = bandwidths[i]
                val previousUpdate = lastUpdateTimes[i]
                if (atTime <= previousUpdate) {
                    continue
                }
                val completePeriods = (atTime - previousUpdate) / bandwidth.refillPeriod
                lastUpdateTimes[i] = previousUpdate + completePeriods * bandwidth.refillPeriod // <= atTime, no overflow
                val currentTokens = tokensPerBandwidth[i] + completePeriods * bandwidth.quantum // TODO: check overflow
                tokensPerBandwidth[i] = if (currentTokens > bandwidth.capacity) {
                    currentTokens % bandwidth.capacity
                } else {
                    currentTokens
                }
            }
        }

        fun addTokens(tokens: Long) {
            for (i in 0..bandwidths.size) {
                val bandwidth = bandwidths[i]
                val capacity = bandwidths[i].capacity
                val newTokens = tokensPerBandwidth[i] + tokens // TODO: check overflow
                tokensPerBandwidth[i] = if (newTokens >= capacity) capacity else newTokens
            }
        }

        fun consume(tokens: Long) = addTokens(-tokens)

        fun nextDeficitCompensationTime(tokens: Long): Long = (0..bandwidths.size)
            .map { i ->
                val currentTokens = tokensPerBandwidth[i]
                val timeToWaitSinceLastUpdate = if (currentTokens >= tokens) {
                    0L
                } else {
                    val deficit = tokens - currentTokens
                    if (deficit <= 0) { // TODO: an overflow happened
                        return@map 0L
                    }
                    val bandwidth = bandwidths[i]
                    val periods = run { // rounding up deficit / bandwidth.quantum
                        val a = deficit / bandwidth.quantum
                        if (a * bandwidth.quantum != deficit) { a + 1 } else { a }
                    }
                    periods * bandwidth.refillPeriod
                }
                lastUpdateTimes[i] + timeToWaitSinceLastUpdate
            }
            .reduce { a, b -> max(a, b) }

        fun returnTokens(takenAtTime: Long, tokens: Long): Boolean {
            val tokensAlreadyCreated = (0..bandwidths.size)
                .map { i ->
                    val bandwidth = bandwidths[i]
                    val completePeriods = (lastEventTime - takenAtTime) / bandwidth.refillPeriod
                    completePeriods * bandwidth.quantum // TODO: check overflow
                }
                .reduce { a, b -> max(a, b) }
            val tokensToRestore = tokens - tokensAlreadyCreated
            if (tokensToRestore > 0) {
                addTokens(tokensToRestore)
                return true
            }
            return false
        }
    }

    val state: AtomicRef<State> = atomic(State(bandwidths))

    private inline fun <T> withState(block: (State) -> T): T {
        while (true) {
            val oldState = state.value
            val currentState = oldState.copyOf()
            val result = block(currentState) // may modify `currentState`
            if (state.compareAndSet(oldState, currentState)) {
                return result
            }
        }
    }

    override fun requestTimeSlot(atTime: Long, tokens: Long, maxDelay: Long): Long = withState { currentState ->
        require(tokens > 0)
        currentState.refill(atTime)
        val deficitCompensationTime = currentState.nextDeficitCompensationTime(tokens)
        if (deficitCompensationTime == Long.MAX_VALUE) {
            return Long.MAX_VALUE
        }
        if (deficitCompensationTime - atTime > maxDelay) {
            return Long.MAX_VALUE
        }
        currentState.consume(tokens)
        deficitCompensationTime
    }

    override fun addTokens(atTime: Long, tokens: Long) = withState { currentState ->
        currentState.refill(atTime)
        currentState.addTokens(tokens)
    }

    override fun relinquishTokens(atTime: Long, takenAtTime: Long, tokens: Long) = withState { currentState ->
        require(tokens > 0)
        currentState.refill(atTime)
        if (!currentState.returnTokens(takenAtTime, tokens)) {
            return // do not loop even if CAS fails
        }
    }
}

public fun rateLimiter(@BuilderInference block: RateLimiterBuilder.() -> Unit): RateLimiter {
    val builder = RateLimiterBuilder()
    builder.block()
    return builder.build()
}

public class RateLimiterBuilder {

    private val bandwidths = mutableListOf<Bandwidth>()

    public fun smooth(capacity: Long, refillPeriod: Long) {
        bandwidths.add(Bandwidth(capacity, refillPeriod / capacity))
    }

    @ExperimentalTime
    public fun smooth(capacity: Long, refillPeriod: Duration) {
        smooth(capacity, refillPeriod.toLongNanoseconds())
    }

    public fun periodic(capacity: Long, refillPeriod: Long, quantum: Long = 1, initialAmount: Long = capacity) {
        bandwidths.add(Bandwidth(capacity, refillPeriod, quantum, initialAmount))
    }

    @ExperimentalTime
    public fun periodic(capacity: Long, refillPeriod: Duration, quantum: Long = 1, initialAmount: Long = capacity) {
        periodic(capacity, refillPeriod.toLongNanoseconds(), quantum, initialAmount)
    }

    internal fun build(): RateLimiter = TokenBucketRateLimiter(bandwidths.toTypedArray())
}
