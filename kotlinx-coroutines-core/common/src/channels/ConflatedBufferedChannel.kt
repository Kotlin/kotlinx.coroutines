/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*
import kotlinx.coroutines.channels.BufferOverflow.*
import kotlinx.coroutines.channels.ChannelResult.Companion.closed
import kotlinx.coroutines.channels.ChannelResult.Companion.success
import kotlinx.coroutines.internal.callUndeliveredElement
import kotlinx.coroutines.internal.OnUndeliveredElement
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*

/**
 * Channel with array buffer of a fixed capacity.
 * Sender suspends only when buffer is full and receiver suspends only when buffer is empty.
 *
 * This channel is created by `Channel(capacity)` factory function invocation.
 *
 * This implementation is blocking and uses coarse-grained locking to protect all channel operations.
 * However, removing a cancelled sender or receiver from a list of waiters is lock-free.
 **/
internal open class ConflatedBufferedChannel<E>(
    private val capacity: Int,
    private val onBufferOverflow: BufferOverflow,
    onUndeliveredElement: OnUndeliveredElement<E>? = null
) : BufferedChannel<E>(capacity = capacity, onUndeliveredElement = onUndeliveredElement) {
    init {
        require(onBufferOverflow !== SUSPEND) {
            "This implementation does not support suspension for senders, use ${BufferedChannel::class.simpleName} instead"
        }
        require(capacity >= 1) {
            "Buffered channel capacity must be at least 1, but $capacity was specified"
        }
    }

    override suspend fun send(element: E) {
        // Should never suspend, implement via `trySend(..)`.
        trySend(element).onClosed { // fails only when this channel is closed.
            onUndeliveredElement?.callUndeliveredElement(element, coroutineContext)
            throw sendException
        }
    }

    override suspend fun sendBroadcast(element: E): Boolean {
        // Should never suspend, implement via `trySend(..)`.
        trySend(element) // fails only when this channel is closed.
            .onSuccess { return true }
            .onClosed { return false }
        error("unreachable")
    }

    override fun trySend(element: E): ChannelResult<Unit> =
        if (onBufferOverflow === DROP_LATEST) trySendDropLatest(element)
        else trySendDropOldest(element)

    private fun trySendDropLatest(element: E): ChannelResult<Unit> {
        // Try to send the element without suspension.
        val result = super.trySend(element)
        // Complete on success or if this channel is closed.
        if (result.isSuccess || result.isClosed) return result
        // This channel is full. Drop the sending element.
        // Call the `onUndeliveredElement` lambda if required
        // and successfully finish.
        onUndeliveredElement?.invoke(element)
        return success(Unit)
    }

    private fun trySendDropOldest(element: E): ChannelResult<Unit> =
        sendImpl( // <-- this is an inline function
            element = element,
            // Put the element into the logical buffer in any case,
            // but if this channel is already full, the `onSuspend`
            // callback below extract the first (oldest) element.
            waiter = BUFFERED,
            // Finish successfully when a rendezvous happens
            // or the element has been buffered.
            onRendezvousOrBuffered = { success(Unit) },
            // In case the algorithm decided to suspend, the element
            // was added to the buffer. However, as the buffer is now
            // overflowed, the first (oldest) element has to be extracted.
            // After that, the operation finishes.
            onSuspend = { segm, i ->
                dropFirstElementsIfNeeded(segm.id * SEGMENT_SIZE + i)
                success(Unit)
            },
            // If the channel is closed, return the corresponding result.
            onClosed = { closed(sendException) }
        )

    @Suppress("UNCHECKED_CAST")
    override fun registerSelectForSend(select: SelectInstance<*>, element: Any?) {
        // The plain `send(..)` operation never suspends. Thus, either this
        // attempt to send the element succeeds or the channel is closed.
        // In any case, complete this `select` in the registration phase.
        trySend(element as E).let {
            it.onSuccess {
                select.selectInRegistrationPhase(Unit)
                return
            }.onClosed {
                select.selectInRegistrationPhase(CHANNEL_CLOSED)
                return
            }
        }
        error("unreachable")
    }

    override fun shouldSendSuspend() = false // never suspends
}
