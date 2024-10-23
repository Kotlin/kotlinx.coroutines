package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.nanoseconds

/**
 * Mode for [ticker] function.
 *
 * **Note: Ticker channels are not currently integrated with structured concurrency and their api will change in the future.**
 */
@ObsoleteCoroutinesApi
public enum class TickerMode {
    /**
     * Adjust delay to maintain fixed period if consumer cannot keep up or is otherwise slow.
     * **This is a default mode.**
     *
     * ```
     * val channel = ticker(delay = 100)
     * delay(350) // 250 ms late
     * println(channel.tryReceive().getOrNull()) // prints Unit
     * println(channel.tryReceive().getOrNull()) // prints null
     *
     * delay(50)
     * println(channel.tryReceive().getOrNull()) // prints Unit, delay was adjusted
     * delay(50)
     * println(channel.tryReceive().getOrNull()) // prints null, we're not late relatively to previous element
     * ```
     */
    FIXED_PERIOD,

    /**
     * Maintains fixed delay between produced elements if consumer cannot keep up or it otherwise slow.
     */
    FIXED_DELAY
}

/**
 * Creates a channel that produces the first item after the given initial delay and subsequent items with the
 * given delay between them.
 *
 * The resulting channel is a _rendezvous channel_. When receiver from this channel does not keep
 * up with receiving the elements from this channel, they are not being sent due to backpressure. The actual
 * timing behavior of ticker in this case is controlled by [mode] parameter which
 * is set to [TickerMode.FIXED_PERIOD] by default. See [TickerMode] for other details.
 *
 * This channel stops producing elements immediately after [ReceiveChannel.cancel] invocation.
 *
 * **Note** producer to this channel is dispatched via [Dispatchers.Unconfined] by default and started eagerly.
 *
 * **Note: Ticker channels are not currently integrated with structured concurrency and their api will change in the future.**
 *           
 * @param delayMillis delay between each element in milliseconds.
 * @param initialDelayMillis delay after which the first element will be produced (it is equal to [delayMillis] by default) in milliseconds.
 * @param context context of the producing coroutine.
 * @param mode specifies behavior when elements are not received ([FIXED_PERIOD][TickerMode.FIXED_PERIOD] by default).
 */
@ObsoleteCoroutinesApi
public fun ticker(
    delayMillis: Long,
    initialDelayMillis: Long = delayMillis,
    context: CoroutineContext = EmptyCoroutineContext,
    mode: TickerMode = TickerMode.FIXED_PERIOD
): ReceiveChannel<Unit> {
    val delay = delayMillis.milliseconds
    val initialDelay = initialDelayMillis.milliseconds
    require(delayMillis >= 0) { "Expected non-negative delay, but got $delay" }
    require(initialDelayMillis >= 0) { "Expected non-negative initial delay, but got $initialDelay" }
    return GlobalScope.produce(Dispatchers.Unconfined + context, capacity = 0) {
        when (mode) {
            TickerMode.FIXED_PERIOD -> fixedPeriodTicker(delay, initialDelay, channel)
            TickerMode.FIXED_DELAY -> fixedDelayTicker(delay, initialDelay, channel)
        }
    }
}

private suspend fun fixedPeriodTicker(
    delay: Duration,
    initialDelay: Duration,
    channel: SendChannel<Unit>
) {
    var deadline = nanoTime() + initialDelay.inWholeNanoseconds
    delay(initialDelay)
    val delayNs = delay.inWholeNanoseconds
    while (true) {
        deadline += delayNs
        channel.send(Unit)
        val now = nanoTime()
        val nextDelay = (deadline - now).coerceAtLeast(0)
        if (nextDelay == 0L && delayNs != 0L) {
            val adjustedDelay = delayNs - (now - deadline) % delayNs
            deadline = now + adjustedDelay
            delay(adjustedDelay.nanoseconds)
        } else {
            delay(nextDelay.nanoseconds)
        }
    }
}

private suspend fun fixedDelayTicker(
    delay: Duration,
    initialDelay: Duration,
    channel: SendChannel<Unit>
) {
    delay(initialDelay)
    while (true) {
        channel.send(Unit)
        delay(delay)
    }
}
