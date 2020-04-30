package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.flow.*
import kotlin.math.*
import kotlin.time.*

public abstract class RateLimiter {
    @ExperimentalTime
    internal abstract fun requestTimeSlot(atTime: Long, tokens: Long, maxDelay: Duration): Long
    internal abstract fun returnTokens(atTime: Long, takenAtTime: Long, tokens: Long)
    internal abstract fun addTokens(atTime: Long, tokens: Long)
}

public fun RateLimiter.addTokens(tokens: Long): Unit = addTokens(nanoTime(), tokens)
public fun RateLimiter.consumeTokens(tokens: Long): Unit = addTokens(-tokens)

@ExperimentalTime
public fun RateLimiter.tryConsume(tokens: Long = 1): Boolean {
    return requestTimeSlot(nanoTime(), tokens, Duration.ZERO) != Long.MAX_VALUE
}

@ExperimentalTime
public suspend fun RateLimiter.consume(tokens: Long = 1, maxDelay: Duration = Duration.INFINITE) {
    val currentTime = nanoTime()
    val nextSlot = requestTimeSlot(currentTime, tokens, maxDelay)
    if (nextSlot == Long.MAX_VALUE) {
        throw UnsupportedOperationException("Could not allocate $tokens tokens in $maxDelay")
    }
    val toSleep = nextSlot - currentTime
    delay(toSleep)
}

public class Reservation internal constructor (private val tokens: Long, private val timeToAct: Long, private val limiter: RateLimiter) {

    private enum class State {
        INITIAL,
        CANCELLED,
        ACTED_ON
    }

    private val state: AtomicRef<State> = atomic(State.INITIAL)

    public suspend fun wait() {
        state.compareAndSet(State.INITIAL, State.ACTED_ON)
        val currentTime = nanoTime()
        val toSleep = timeToAct - currentTime
        delay(toSleep)
    }

    public suspend fun cancel() {
        state.compareAndSet(State.INITIAL, State.CANCELLED)
        limiter.returnTokens(nanoTime(), timeToAct, tokens)
    }
}

@ExperimentalTime
public suspend fun RateLimiter.getReservation(tokens: Long = 1, maxDelay: Duration = Duration.INFINITE): Reservation? {
    val nextSlot = requestTimeSlot(nanoTime(), tokens, maxDelay)
    if (nextSlot == Long.MAX_VALUE) {
        return null
    }
    return Reservation(tokens, nextSlot, this)
}

internal class RateLimitedFlow<T>(
    val flow: Flow<T>, private val rateLimiter: RateLimiter, private val tokensPerValue: (T) -> Long): Flow<T> {
    @ExperimentalTime
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

internal class TokenBucketRateLimiter(bandwidths: Array<Bandwidth>): RateLimiter() {

    internal class Bandwidth(
        val capacity: Long, val refillPeriod: Long, val quantum: Long = 1, val initialAmount: Long = capacity) {
    }

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
                val timeToWait = if (currentTokens >= tokens) {
                    0L
                } else {
                    val deficit = tokens - currentTokens
                    if (deficit <= 0) { // an overflow happened
                        return@map 0L
                    }
                    val bandwidth = bandwidths[i]
                    val periods = run { // rounding up deficit / bandwidth.quantum
                        val a = deficit / bandwidth.quantum
                        if (a * bandwidth.quantum != deficit) { a + 1 } else { a }
                    }
                    periods * bandwidth.refillPeriod
                }
                lastUpdateTimes[i] + timeToWait
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

    @ExperimentalTime
    override fun requestTimeSlot(atTime: Long, tokens: Long, maxDelay: Duration): Long = withState { currentState ->
        require(tokens > 0)
        currentState.refill(atTime)
        val deficitCompensationTime = currentState.nextDeficitCompensationTime(tokens)
        if (deficitCompensationTime == Long.MAX_VALUE) {
            return Long.MAX_VALUE
        }
        if (deficitCompensationTime - atTime > maxDelay.toLongNanoseconds()) {
            return Long.MAX_VALUE
        }
        currentState.consume(tokens)
        deficitCompensationTime
    }

    override fun addTokens(atTime: Long, tokens: Long) = withState { currentState ->
        currentState.refill(atTime)
        currentState.addTokens(tokens)
    }

    override fun returnTokens(atTime: Long, takenAtTime: Long, tokens: Long) = withState { currentState ->
        require(tokens > 0)
        currentState.refill(atTime)
        if (!currentState.returnTokens(takenAtTime, tokens)) {
            return // do not loop even if CAS fails
        }
    }
}
