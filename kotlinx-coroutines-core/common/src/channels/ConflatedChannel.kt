/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*

/**
 * Channel that buffers at most one element and conflates all subsequent `send` and `offer` invocations,
 * so that the receiver always gets the most recently sent element.
 * Back-to-send sent elements are _conflated_ -- only the most recently sent element is received,
 * while previously sent elements **are lost**.
 * Sender to this channel never suspends and [offer] always returns `true`.
 *
 * This channel is created by `Channel(Channel.CONFLATED)` factory function invocation.
 */
internal open class ConflatedChannel<E>(onUndeliveredElement: OnUndeliveredElement<E>?) : AbstractChannel<E>(onUndeliveredElement) {
    protected final override val isBufferAlwaysEmpty: Boolean get() = false
    protected final override val isBufferEmpty: Boolean get() = value === EMPTY
    protected final override val isBufferAlwaysFull: Boolean get() = false
    protected final override val isBufferFull: Boolean get() = false

    override val isEmpty: Boolean get() = lock.withLock { isEmptyImpl }

    private val lock = ReentrantLock()

    private var value: Any? = EMPTY

    // result is `OFFER_SUCCESS | Closed`
    protected override fun offerInternal(element: E): Any {
        var receive: ReceiveOrClosed<E>? = null
        lock.withLock {
            closedForSend?.let { return it }
            // if there is no element written in buffer
            if (value === EMPTY) {
                // check for receivers that were waiting on the empty buffer
                loop@ while(true) {
                    receive = takeFirstReceiveOrPeekClosed() ?: break@loop // break when no receivers queued
                    if (receive is Closed) {
                        return receive!!
                    }
                    val token = receive!!.tryResumeReceive(element, null)
                    if (token != null) {
                        assert { token === RESUME_TOKEN }
                        return@withLock
                    }
                }
            }
            updateValueLocked(element)?.let { throw it }
            return OFFER_SUCCESS
        }
        // breaks here if offer meets receiver
        receive!!.completeResumeReceive(element)
        return receive!!.offerResult
    }

    // result is `ALREADY_SELECTED | OFFER_SUCCESS | Closed`
    protected override fun offerSelectInternal(element: E, select: SelectInstance<*>): Any {
        var receive: ReceiveOrClosed<E>? = null
        lock.withLock {
            closedForSend?.let { return it }
            if (value === EMPTY) {
                loop@ while(true) {
                    val offerOp = describeTryOffer(element)
                    val failure = select.performAtomicTrySelect(offerOp)
                    when {
                        failure == null -> { // offered successfully
                            receive = offerOp.result
                            return@withLock
                        }
                        failure === OFFER_FAILED -> break@loop // cannot offer -> Ok to queue to buffer
                        failure === RETRY_ATOMIC -> {} // retry
                        failure === ALREADY_SELECTED || failure is Closed<*> -> return failure
                        else -> error("performAtomicTrySelect(describeTryOffer) returned $failure")
                    }
                }
            }
            // try to select sending this element to buffer
            if (!select.trySelect()) {
                return ALREADY_SELECTED
            }
            updateValueLocked(element)?.let { throw it }
            return OFFER_SUCCESS
        }
        // breaks here if offer meets receiver
        receive!!.completeResumeReceive(element)
        return receive!!.offerResult
    }

    // result is `E | POLL_FAILED | Closed`
    protected override fun pollInternal(): Any? {
        var result: Any? = null
        lock.withLock {
            if (value === EMPTY) return closedForSend ?: POLL_FAILED
            result = value
            value = EMPTY
        }
        return result
    }

    // result is `E | POLL_FAILED | Closed`
    protected override fun pollSelectInternal(select: SelectInstance<*>): Any? {
        var result: Any? = null
        lock.withLock {
            if (value === EMPTY) return closedForSend ?: POLL_FAILED
            if (!select.trySelect())
                return ALREADY_SELECTED
            result = value
            value = EMPTY
        }
        return result
    }

    protected override fun onCancelIdempotent(wasClosed: Boolean) {
        var undeliveredElementException: UndeliveredElementException? = null // resource cancel exception
        lock.withLock {
            undeliveredElementException = updateValueLocked(EMPTY)
        }
        super.onCancelIdempotent(wasClosed)
        undeliveredElementException?.let { throw it } // throw exception at the end if there was one
    }

    private fun updateValueLocked(element: Any?): UndeliveredElementException? {
        val old = value
        val undeliveredElementException = if (old === EMPTY) null else
            onUndeliveredElement?.callUndeliveredElementCatchingException(old as E)
        value = element
        return undeliveredElementException
    }

    override fun enqueueReceiveInternal(receive: Receive<E>): Boolean = lock.withLock {
        super.enqueueReceiveInternal(receive)
    }

    // ------ debug ------

    override val bufferDebugString: String
        get() = "(value=$value)"
}
