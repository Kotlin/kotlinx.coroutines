package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.timeunit.*
import kotlin.coroutines.experimental.*

/**
 * Mode for [ticker] function.
 */
enum class TickerMode {
    /**
     * Adjust delay to maintain fixed period if consumer cannot keep up or is otherwise slow.
     * **This is a default mode.**
     *
     * ```
     * val channel = ticker(delay = 100)
     * delay(350) // 250 ms late
     * println(channel.poll()) // prints Unit
     * println(channel.poll()) // prints null
     *
     * delay(50)
     * println(channel.poll()) // prints Unit, delay was adjusted
     * delay(50)
     * println(channel.poll()) // prints null, we'are not late relatively to previous element
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
 * The resulting channel is a [rendezvous channel][RendezvousChannel]. When receiver from this channel does not keep
 * up with receiving the elements from this channel, they are not being being send due to backpressure. The actual
 * timing behavior of ticker in this case is controlled by [mode] parameter which
 * is set to [TickerMode.FIXED_PERIOD] by default. See [TickerMode] for other details.
 *
 * This channel stops producing elements immediately after [ReceiveChannel.cancel] invocation.
 *
 * **Note** producer to this channel is dispatched via [Unconfined] dispatcher by default and started eagerly.
 *
 * @param delay delay between each element.
 * @param unit unit of time that applies to [initialDelay] and [delay] (in milliseconds by default).
 * @param initialDelay delay after which the first element will be produced (it is equal to [delay] by default).
 * @param context context of the producing coroutine.
 * @param mode specifies behavior when elements are not received ([FIXED_PERIOD][TickerMode.FIXED_PERIOD] by default).
 */
public fun ticker(
    delay: Long,
    unit: TimeUnit = TimeUnit.MILLISECONDS,
    initialDelay: Long = delay,
    context: CoroutineContext = EmptyCoroutineContext,
    mode: TickerMode = TickerMode.FIXED_PERIOD
): ReceiveChannel<Unit> {
    require(delay >= 0) { "Expected non-negative delay, but has $delay" }
    require(initialDelay >= 0) { "Expected non-negative initial delay, but has $initialDelay" }
    return produce(Unconfined + context, capacity = 0) {
        when(mode) {
            TickerMode.FIXED_PERIOD -> fixedPeriodTicker(delay, unit, initialDelay, channel)
            TickerMode.FIXED_DELAY -> fixedDelayTicker(delay, unit, initialDelay, channel)
        }
    }
}

private suspend fun fixedPeriodTicker(
    delay: Long,
    unit: TimeUnit,
    initialDelay: Long,
    channel: SendChannel<Unit>
) {
    var deadline = timeSource.nanoTime() + unit.toNanos(initialDelay)
    delay(initialDelay, unit)
    val delayNs = unit.toNanos(delay)
    while (true) {
        deadline += delayNs
        channel.send(Unit)
        val now = timeSource.nanoTime()
        val nextDelay = (deadline - now).coerceAtLeast(0)
        if (nextDelay == 0L && delayNs != 0L) {
            val adjustedDelay = delayNs - (now - deadline) % delayNs
            deadline = now + adjustedDelay
            delay(adjustedDelay, java.util.concurrent.TimeUnit.NANOSECONDS)
        } else {
            delay(nextDelay, java.util.concurrent.TimeUnit.NANOSECONDS)
        }
    }
}

private suspend fun fixedDelayTicker(
    delay: Long,
    unit: TimeUnit,
    initialDelay: Long,
    channel: SendChannel<Unit>
) {
    delay(initialDelay, unit)
    while (true) {
        channel.send(Unit)
        delay(delay, unit)
    }
}
