/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.selects.*
import kotlinx.coroutines.internal.*

/**
 * Channel that buffers at most one element and conflates all subsequent `send` and `offer` invocations,
 * so that the receiver always gets the most recently sent element.
 * Back-to-send sent elements are _conflated_ -- only the the most recently sent element is received,
 * while previously sent elements **are lost**.
 * Sender to this channel never suspends and [offer] always returns `true`.
 *
 * This channel is created by `Channel(Channel.CONFLATED)` factory function invocation.
 *
 * This implementation is fully lock-free.
 */
internal open class ConflatedChannel<E> : AbstractChannel<E>() {
    protected final override val isBufferAlwaysEmpty: Boolean get() = true
    protected final override val isBufferEmpty: Boolean get() = true
    protected final override val isBufferAlwaysFull: Boolean get() = false
    protected final override val isBufferFull: Boolean get() = false

    override fun onClosedIdempotent(closed: LockFreeLinkedListNode) {
        conflatePreviousSendBuffered(closed)
    }

    // result is always `OFFER_SUCCESS | Closed`
    protected override fun offerInternal(element: E): Any {
        while (true) {
            val result = super.offerInternal(element)
            when {
                result === OFFER_SUCCESS -> return OFFER_SUCCESS
                result === OFFER_FAILED -> { // try to buffer
                    val sendResult = sendConflated(element)
                    when (sendResult) {
                        null -> return OFFER_SUCCESS
                        is Closed<*> -> {
                            conflatePreviousSendBuffered(sendResult)
                            return sendResult
                        }
                    }
                    // otherwise there was receiver in queue, retry super.offerInternal
                }
                result is Closed<*> -> {
                    conflatePreviousSendBuffered(result)
                    return result
                }
                else -> error("Invalid offerInternal result $result")
            }
        }
    }

    // result is always `ALREADY_SELECTED | OFFER_SUCCESS | Closed`.
    protected override fun offerSelectInternal(element: E, select: SelectInstance<*>): Any {
        while (true) {
            val result = if (hasReceiveOrClosed)
                super.offerSelectInternal(element, select) else
                (select.performAtomicTrySelect(describeSendConflated(element)) ?: OFFER_SUCCESS)
            when {
                result === ALREADY_SELECTED -> return ALREADY_SELECTED
                result === OFFER_SUCCESS -> return OFFER_SUCCESS
                result === OFFER_FAILED -> {} // retry
                result is Closed<*> -> {
                    conflatePreviousSendBuffered(result)
                    return result
                }
                else -> error("Invalid result $result")
            }
        }
    }
}
