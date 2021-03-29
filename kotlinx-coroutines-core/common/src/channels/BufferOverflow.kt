/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*

/**
 * A strategy for buffer overflow handling in [channels][Channel] and [flows][kotlinx.coroutines.flow.Flow] that
 * controls what is going to be sacrificed on buffer overflow:
 *
 * * [SUSPEND] &mdash; the upstream that is [sending][SendChannel.send] or
 *   is [emitting][kotlinx.coroutines.flow.FlowCollector.emit] a value is **suspended** while the buffer is full.
 * * [DROP_OLDEST] &mdash; drop **the oldest** value in the buffer on overflow, add the new value to the buffer, do not suspend.
 * * [DROP_LATEST] &mdash; drop **the latest** value that is being added to the buffer right now on buffer overflow
 *   (so that buffer contents stay the same), do not suspend.
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
