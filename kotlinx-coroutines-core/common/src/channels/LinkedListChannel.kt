/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*

/**
 * Channel with linked-list buffer of a unlimited capacity (limited only by available memory).
 * Sender to this channel never suspends and [trySend] always succeeds.
 *
 * This channel is created by `Channel(Channel.UNLIMITED)` factory function invocation.
 *
 * This implementation is fully lock-free.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
internal open class LinkedListChannel<E>(onUndeliveredElement: OnUndeliveredElement<E>?) : AbstractChannel<E>(onUndeliveredElement) {
    protected final override val isBufferAlwaysEmpty: Boolean get() = true
    protected final override val isBufferEmpty: Boolean get() = true
    protected final override val isBufferAlwaysFull: Boolean get() = false
    protected final override val isBufferFull: Boolean get() = false

    // result is always `OFFER_SUCCESS | Closed`
    protected override fun offerInternal(element: E): Any {
        while (true) {
            val result = super.offerInternal(element)
            when {
                result === OFFER_SUCCESS -> return OFFER_SUCCESS
                result === OFFER_FAILED -> { // try to buffer
                    when (val sendResult = sendBuffered(element)) {
                        null -> return OFFER_SUCCESS
                        is Closed<*> -> return sendResult
                    }
                    // otherwise there was receiver in queue, retry super.offerInternal
                }
                result is Closed<*> -> return result
                else -> error("Invalid offerInternal result $result")
            }
        }
    }

    // result is always `ALREADY_SELECTED | OFFER_SUCCESS | Closed`.
    protected override fun offerSelectInternal(element: E, select: SelectInstance<*>): Any {
        while (true) {
            val result = if (hasReceiveOrClosed)
                super.offerSelectInternal(element, select) else
                (select.performAtomicTrySelect(describeSendBuffered(element)) ?: OFFER_SUCCESS)
            when {
                result === ALREADY_SELECTED -> return ALREADY_SELECTED
                result === OFFER_SUCCESS -> return OFFER_SUCCESS
                result === OFFER_FAILED -> {} // retry
                result === RETRY_ATOMIC -> {} // retry
                result is Closed<*> -> return result
                else -> error("Invalid result $result")
            }
        }
    }

    override fun onCancelIdempotentList(list: InlineList<Send>, closed: Closed<*>) {
        var undeliveredElementException: UndeliveredElementException? = null
        list.forEachReversed {
            when (it) {
                is SendBuffered<*> -> {
                    @Suppress("UNCHECKED_CAST")
                    undeliveredElementException = onUndeliveredElement?.callUndeliveredElementCatchingException(it.element as E, undeliveredElementException)
                }
                else -> it.resumeSendClosed(closed)
            }
        }
        undeliveredElementException?.let { throw it } // throw UndeliveredElementException at the end if there was one
    }
}

