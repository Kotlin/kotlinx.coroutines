/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*

/**
 * Channel that buffers at most one element and conflates all subsequent `send` and `trySend` invocations,
 * so that the receiver always gets the most recently sent element.
 * Back-to-send sent elements are _conflated_ -- only the most recently sent element is received,
 * while previously sent elements **are lost**.
 * Sender to this channel never suspends and [trySend] always succeeds.
 *
 * This channel is created by `Channel(Channel.CONFLATED)` factory function invocation.
 */
internal open class ConflatedChannel<E>(onUndeliveredElement: OnUndeliveredElement<E>?) : AbstractChannel<E>(onUndeliveredElement) {
    protected final override val isBufferAlwaysEmpty: Boolean get() = false
    protected final override val isBufferEmpty: Boolean get() = lock.withLock { value === EMPTY }
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
                    val token = receive!!.tryResumeReceive(element)
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

    protected override fun onCancelIdempotent(wasClosed: Boolean) {
        var undeliveredElementException: UndeliveredElementException? = null // resource cancel exception
        lock.withLock {
            undeliveredElementException = updateValueLocked(EMPTY)
        }
        super.onCancelIdempotent(wasClosed)
        undeliveredElementException?.let { throw it } // throw UndeliveredElementException at the end if there was one
    }

    @Suppress("UNCHECKED_CAST")
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
        get() = lock.withLock { "(value=$value)" }
}
