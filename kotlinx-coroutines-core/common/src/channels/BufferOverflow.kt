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
     */
    SUSPEND,

    /**
     * Drop **the oldest** value in the buffer on overflow, add the new value to the buffer, do not suspend.
     */
    DROP_OLDEST,

    /**
     * Drop **the latest** value that is being added to the buffer right now on buffer overflow
     * (so that buffer contents stay the same), do not suspend.
     */
    DROP_LATEST
}
