package kotlinx.coroutines.channels

/**
 * A strategy for buffer overflow handling in [channels][Channel] and [flows][kotlinx.coroutines.flow.Flow] that
 * controls what is going to be sacrificed on buffer overflow:
 *
 * - [SUSPEND] &mdash; the upstream that is [sending][SendChannel.send] or
 *   is [emitting][kotlinx.coroutines.flow.FlowCollector.emit] a value is **suspended** while the buffer is full.
 * - [DROP_OLDEST] &mdash; **the oldest** value in the buffer is dropped on overflow, and the new value is added,
 *   all without suspending.
 * - [DROP_LATEST] &mdash; the buffer remains unchanged on overflow, and the value that we were going to add
 *   gets discarded, all without suspending.
 */
public enum class BufferOverflow {
    /**
     * Suspend on buffer overflow.
     *
     * Use this to create backpressure, forcing the producers to slow down creation of new values in response to
     * consumers not being able to process the incoming values in time.
     * [SUSPEND] is a good choice when all elements must eventually be processed.
     */
    SUSPEND,

    /**
     * Drop **the oldest** value in the buffer on overflow, add the new value to the buffer, do not suspend.
     *
     * Use this in scenarios when only the last few values are important and skipping the processing of severely
     * outdated ones is desirable.
     */
    DROP_OLDEST,

    /**
     * Leave the buffer unchanged on overflow, dropping the value that we were going to add, do not suspend.
     *
     * This option can be used in rare advanced scenarios where all elements that are expected to enter the buffer are
     * equal, so it is not important which of them get thrown away.
     */
    DROP_LATEST
}
