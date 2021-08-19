/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.channels.BufferOverflow.*
import kotlinx.coroutines.internal.*

/**
 * Channel with array buffer of a fixed capacity.
 * Sender suspends only when buffer is full and receiver suspends only when buffer is empty.
 *
 * This channel is created by `Channel(capacity)` factory function invocation.
 *
 * This implementation uses lock to protect the buffer, which is held only during very short buffer-update operations.
 * The lists of suspended senders or receivers are lock-free.
 **/
internal open class ArrayChannel<E>(
    /**
     * Buffer capacity.
     */
    capacity: Int,
    val onBufferOverflow: BufferOverflow,
    onUndeliveredElement: OnUndeliveredElement<E>?
) : BufferedChannel<E>(capacity = capacity, onUndeliveredElement = onUndeliveredElement) {
    override fun trySend(element: E): ChannelResult<Unit> = when(onBufferOverflow) {
        DROP_OLDEST -> {
            TODO()
        }
        DROP_LATEST -> {
            val result = super.trySend(element)
            if (result.isClosed || result.isSuccess) result
            else ChannelResult.success(Unit)
        }
        SUSPEND -> super.trySend(element)
    }

    override suspend fun send(element: E) {
        when(onBufferOverflow) {
            DROP_OLDEST -> {
                trySend(element)
            }
            DROP_LATEST -> {
                trySend(element)
            }
            SUSPEND -> {
                super.send(element)
            }
        }
    }
}
