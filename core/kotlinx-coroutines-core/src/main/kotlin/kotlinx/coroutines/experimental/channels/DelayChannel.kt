package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.timeunit.*


/**
 * Creates rendezvous channel which emits the first item after the given initial delay and subsequent items with the
 * given delay between emissions. Backpressure is guaranteed by [RendezvousChannel], but no upper bound on actual delay is guaranteed.
 * If the consumer of this channel cannot keep up with given delay
 * and spends more than [delay] between subsequent invocations to [ReceiveChannel.receive] then rate and a maximum delay
 * of outcoming events will be limited by the consumer.
 *
 * This channel stops emission immediately after [ReceiveChannel.cancel] invocation.
 * **Note** producer to this channel is dispatched via [Unconfined] dispatcher and started eagerly
 *
 * @param initialDelay delay after which the first item will be emitted
 * @param delay delay between
 * @param unit unit of time that applies to [initialDelay] and [delay]
 */
public fun DelayChannel(
    delay: Long,
    unit: TimeUnit = TimeUnit.MILLISECONDS,
    initialDelay: Long = 0
): ReceiveChannel<Unit> {
    require(delay >= 0) { "Expected non-negative delay, but has $delay" }
    require(initialDelay >= 0) { "Expected non-negative initial delay, but has $initialDelay" }

    val result = RendezvousChannel<Unit>()
    launch(start = CoroutineStart.UNDISPATCHED) {
        delay(initialDelay, unit)
        while (true) {
            val sendTime = timeSource.nanoTime()
            result.send(Unit)
            val queueTime = timeSource.nanoTime() - sendTime
            val nextDelay = (unit.toNanos(delay) - queueTime).coerceAtLeast(0L)
            delay(nextDelay, java.util.concurrent.TimeUnit.NANOSECONDS)
        }
    }

    return result
}

/**
 * Creates rendezvous channel which emits the first item after the given initial delay and subsequent items with the
 * given delay after consumption of previously emitted item. Backpressure is guaranteed by [RendezvousChannel] machinery.
 * This channel stops emitting items immediately after [ReceiveChannel.cancel] invocation.
 * **Note** producer to this channel is dispatched via [Unconfined] dispatcher and started eagerly
 *
 * @param initialDelay delay after which the first item will be emitted
 * @param delay delay between
 * @param unit unit of time that applies to [initialDelay] and [delay]
 */
public fun FixedDelayChannel(
    delay: Long,
    unit: TimeUnit = TimeUnit.MILLISECONDS,
    initialDelay: Long = 0
): ReceiveChannel<Unit> {
    require(delay >= 0) { "Expected non-negative delay, but has $delay" }
    require(initialDelay >= 0) { "Expected non-negative initial delay, but has $initialDelay" }

    val result = RendezvousChannel<Unit>()
    launch(context = Unconfined) {
        delay(initialDelay, unit)
        while (true) {
            result.send(Unit)
            delay(delay, unit)
        }
    }

    return result
}
