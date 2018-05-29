package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.timeunit.*
import kotlin.coroutines.experimental.*


/**
 * Creates rendezvous channel which produces the first item after the given initial delay and subsequent items with the
 * given delay between them. Backpressure is guaranteed by [RendezvousChannel].
 *
 * This channel stops producing elements immediately after [ReceiveChannel.cancel] invocation.
 * **Note** producer to this channel is dispatched via [Unconfined] dispatcher and started eagerly
 *
 * @param initialDelay delay after which the first item will be produced
 * @param delay delay between each element
 * @param unit unit of time that applies to [initialDelay] and [delay]
 * @param coroutineContext context of the producing coroutine
 * @param fixedPeriod whether producer should use fixed delay or should attempt to adjust delay when consumer cannot keep up
 */
public fun ticker(
    delay: Long,
    unit: TimeUnit = TimeUnit.MILLISECONDS,
    initialDelay: Long = delay,
    coroutineContext: CoroutineContext = Unconfined,
    fixedPeriod: Boolean = false
): ReceiveChannel<Unit> {
    return if (fixedPeriod) fixedTicker(delay, unit, initialDelay, coroutineContext)
    else adjustingTicker(delay, unit, initialDelay, coroutineContext)
}

/**
 * Creates rendezvous channel which produces the first item after the given initial delay and subsequent items after
 * given delay.
 *
 * Producer to resulting channel tries to adjust delay if consumer cannot keep up:
 * ```
 * val channel = adjustingTicker(delay = 100)
 * delay(350) // 250 ms late
 * println(channel.poll()) // prints Unit
 * println(channel.poll()) // prints null
 *
 * delay(50)
 * println(channel.poll() // prints Unit, delay was adjusted
 * delay(50)
 * println(channel.poll() // prints null, we'are not late relatively to previous element
 * ```
 *
 * This channel stops producing elements immediately after [ReceiveChannel.cancel] invocation.
 * **Note** producer to this channel is dispatched via [Unconfined] dispatcher and started eagerly
 *
 * @param initialDelay delay after which the first item will be produced
 * @param delay delay between each elements
 * @param unit unit of time that applies to [initialDelay] and [delay]
 * @param coroutineContext context of the producing coroutine
 */
public fun adjustingTicker(
    delay: Long,
    unit: TimeUnit = TimeUnit.MILLISECONDS,
    initialDelay: Long = delay,
    coroutineContext: CoroutineContext = Unconfined
): ReceiveChannel<Unit> {
    require(delay >= 0) { "Expected non-negative delay, but has $delay" }
    require(initialDelay >= 0) { "Expected non-negative initial delay, but has $initialDelay" }

    val result = RendezvousChannel<Unit>()
    launch(coroutineContext) {
        delay(initialDelay, unit)

        val delayNs = unit.toNanos(delay)
        var deadline = timeSource.nanoTime()
        while (true) {
            deadline += delayNs
            result.send(Unit)
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

    return result
}

/**
 * Creates rendezvous channel which produces the first item after the given initial delay and subsequent items after
 * given delay **after** consumption of the previous item.
 *
 * This channel stops producing elements immediately after [ReceiveChannel.cancel] invocation.
 * **Note** producer to this channel is dispatched via [Unconfined] dispatcher and started eagerly
 *
 * @param initialDelay delay after which the first item will be produced
 * @param delay delay between each elements
 * @param unit unit of time that applies to [initialDelay] and [delay]
 * @param coroutineContext context of the producing coroutine
 */
public fun fixedTicker(
    delay: Long,
    unit: TimeUnit = TimeUnit.MILLISECONDS,
    initialDelay: Long = delay,
    coroutineContext: CoroutineContext = Unconfined
): ReceiveChannel<Unit> {
    require(delay >= 0) { "Expected non-negative delay, but has $delay" }
    require(initialDelay >= 0) { "Expected non-negative initial delay, but has $initialDelay" }

    val result = RendezvousChannel<Unit>()
    launch(coroutineContext) {
        delay(initialDelay, unit)
        while (true) {
            result.send(Unit)
            delay(delay, unit)
        }
    }

    return result
}
