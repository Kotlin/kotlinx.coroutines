/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.math.*

/**
 * Channel with array buffer of a fixed [capacity].
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
    private val capacity: Int,
    private val onBufferOverflow: BufferOverflow,
    onUndeliveredElement: OnUndeliveredElement<E>?
) : AbstractChannel<E>(onUndeliveredElement) {
    init {
        // This check is actually used by the Channel(...) constructor function which checks only for known
        // capacities and calls ArrayChannel constructor for everything else.
        require(capacity >= 1) { "ArrayChannel capacity must be at least 1, but $capacity was specified" }
    }

    /*
     * Allocate minimum of capacity and 8 to avoid excess memory pressure for large channels when it's not necessary.
     */
    private val state = ArrayChannelState(min(capacity, 8))

    protected final override val isBufferAlwaysEmpty: Boolean get() = false
    protected final override val isBufferEmpty: Boolean get() = state.size == 0
    protected final override val isBufferAlwaysFull: Boolean get() = false
    protected final override val isBufferFull: Boolean get() = state.size == capacity

    override val isEmpty: Boolean get() = state.withLock { isEmptyImpl }
    override val isClosedForReceive: Boolean get() = state.withLock { super.isClosedForReceive }

    // result is `OFFER_SUCCESS | OFFER_FAILED | Closed`
    protected override fun offerInternal(element: E): Any {
        var receive: ReceiveOrClosed<E>? = null
        state.withLock {
            val size = state.size
            closedForSend?.let { return it }
            // update size before checking queue (!!!)
            updateBufferSize(size)?.let { return it }
            // check for receivers that were waiting on empty queue
            if (size == 0) {
                loop@ while (true) {
                    receive = takeFirstReceiveOrPeekClosed() ?: break@loop // break when no receivers queued
                    if (receive is Closed) {
                        state.size = size // restore size
                        return receive!!
                    }
                    val token = receive!!.tryResumeReceive(element, null)
                    if (token != null) {
                        assert { token === RESUME_TOKEN }
                        state.size = size // restore size
                        return@withLock
                    }
                }
            }
            enqueueElement(size, element)
            return OFFER_SUCCESS
        }
        // breaks here if offer meets receiver
        receive!!.completeResumeReceive(element)
        return receive!!.offerResult
    }

    // result is `ALREADY_SELECTED | OFFER_SUCCESS | OFFER_FAILED | Closed`
    protected override fun offerSelectInternal(element: E, select: SelectInstance<*>): Any {
        var receive: ReceiveOrClosed<E>? = null
        state.withLock {
            val size = state.size
            closedForSend?.let { return it }
            // update size before checking queue (!!!)
            updateBufferSize(size)?.let { return it }
            // check for receivers that were waiting on empty queue
            if (size == 0) {
                loop@ while (true) {
                    val offerOp = describeTryOffer(element)
                    val failure = select.performAtomicTrySelect(offerOp)
                    when {
                        failure == null -> { // offered successfully
                            state.size = size // restore size
                            receive = offerOp.result
                            return@withLock
                        }
                        failure === OFFER_FAILED -> break@loop // cannot offer -> Ok to queue to buffer
                        failure === RETRY_ATOMIC -> {} // retry
                        failure === ALREADY_SELECTED || failure is Closed<*> -> {
                            state.size = size // restore size
                            return failure
                        }
                        else -> error("performAtomicTrySelect(describeTryOffer) returned $failure")
                    }
                }
            }
            // let's try to select sending this element to buffer
            if (!select.trySelect()) { // :todo: move trySelect completion outside of lock
                state.size = size // restore size
                return ALREADY_SELECTED
            }
            enqueueElement(size, element)
            return OFFER_SUCCESS
        }
        // breaks here if offer meets receiver
        receive!!.completeResumeReceive(element)
        return receive!!.offerResult
    }

    override fun enqueueSend(send: Send): Any? = state.withLock {
        super.enqueueSend(send)
    }

    // Guarded by lock
    // Result is `OFFER_SUCCESS | OFFER_FAILED | null`
    private fun updateBufferSize(currentSize: Int): Symbol? {
        if (currentSize < capacity) {
            state.size = currentSize + 1 // tentatively put it into the buffer
            return null // proceed
        }
        // buffer is full
        return when (onBufferOverflow) {
            BufferOverflow.SUSPEND -> OFFER_FAILED
            BufferOverflow.DROP_LATEST -> OFFER_SUCCESS
            BufferOverflow.DROP_OLDEST -> null // proceed, will drop oldest in enqueueElement
        }
    }

    // Guarded by lock
    private fun enqueueElement(currentSize: Int, element: E) {
        if (currentSize < capacity) {
            state.ensureCapacity(currentSize, capacity)
            state.setBufferAt((state.head + currentSize) % state.bufferSize, element) // actually queue element
        } else {
            // buffer is full
            assert { onBufferOverflow == BufferOverflow.DROP_OLDEST } // the only way we can get here
            state.setBufferAt(state.head % state.bufferSize, null) // drop oldest element
            state.setBufferAt((state.head + currentSize) % state.bufferSize, element) // actually queue element
            // actually queue element
            state.head = (state.head + 1) % state.bufferSize
        }
    }

    // result is `E | POLL_FAILED | Closed`
    protected override fun pollInternal(): Any? {
        var send: Send? = null
        var resumed = false
        var result: Any? = null
        state.withLock {
            val size = state.size
            if (size == 0) return closedForSend ?: POLL_FAILED // when nothing can be read from buffer
            // size > 0: not empty -- retrieve element
            result = state.getBufferAt(state.head)
            state.setBufferAt(state.head, null)
            state.size = size - 1 // update size before checking queue (!!!)
            // check for senders that were waiting on full queue
            var replacement: Any? = POLL_FAILED
            if (size == capacity) {
                loop@ while (true) {
                    send = takeFirstSendOrPeekClosed() ?: break
                    disposeQueue { send as? Closed<*> }
                    val token = send!!.tryResumeSend(null)
                    if (token != null) {
                        assert { token === RESUME_TOKEN }
                        resumed = true
                        replacement = send!!.pollResult
                        break@loop
                    }
                    // too late, already cancelled, but we removed it from the queue and need to notify on undelivered element
                    send!!.undeliveredElement()
                }
            }
            if (replacement !== POLL_FAILED && replacement !is Closed<*>) {
                state.size = size // restore size
                state.setBufferAt((state.head + size) % state.bufferSize, replacement)
            }
            state.head = (state.head + 1) % state.bufferSize
        }
        // complete send the we're taken replacement from
        if (resumed)
            send!!.completeResumeSend()
        return result
    }

    // result is `ALREADY_SELECTED | E | POLL_FAILED | Closed`
    protected override fun pollSelectInternal(select: SelectInstance<*>): Any? {
        var send: Send? = null
        var success = false
        var result: Any? = null
        state.withLock {
            val size = state.size
            if (size == 0) return closedForSend ?: POLL_FAILED
            // size > 0: not empty -- retrieve element
            result = state.getBufferAt(state.head)
            state.setBufferAt(state.head, null)
            state.size = size - 1 // update size before checking queue (!!!)
            // check for senders that were waiting on full queue
            var replacement: Any? = POLL_FAILED
            if (size == capacity) {
                loop@ while (true) {
                    val pollOp = describeTryPoll()
                    val failure = select.performAtomicTrySelect(pollOp)
                    when {
                        failure == null -> { // polled successfully
                            send = pollOp.result
                            success = true
                            replacement = send!!.pollResult
                            break@loop
                        }
                        failure === POLL_FAILED -> break@loop // cannot poll -> Ok to take from buffer
                        failure === RETRY_ATOMIC -> {} // retry
                        failure === ALREADY_SELECTED -> {
                            state.size = size // restore size
                            state.setBufferAt(state.head, result) // restore head
                            return failure
                        }
                        failure is Closed<*> -> {
                            send = failure
                            success = true
                            replacement = failure
                            break@loop
                        }
                        else -> error("performAtomicTrySelect(describeTryOffer) returned $failure")
                    }
                }
            }
            if (replacement !== POLL_FAILED && replacement !is Closed<*>) {
                state.size = size // restore size
                state.setBufferAt((state.head + size) % state.bufferSize, replacement)
            } else {
                // failed to poll or is already closed --> let's try to select receiving this element from buffer
                if (!select.trySelect()) { // :todo: move trySelect completion outside of lock
                    state.size = size // restore size
                    state.setBufferAt(state.head, result) // restore head
                    return ALREADY_SELECTED
                }
            }
            state.head = (state.head + 1) % state.bufferSize
        }
        // complete send the we're taken replacement from
        if (success)
            send!!.completeResumeSend()
        return result
    }

    override fun enqueueReceiveInternal(receive: Receive<E>): Boolean = state.withLock {
        super.enqueueReceiveInternal(receive)
    }

    // Note: this function is invoked when channel is already closed
    override fun onCancelIdempotent(wasClosed: Boolean) {
        // clear buffer first, but do not wait for it in helpers
        val onUndeliveredElement = onUndeliveredElement
        var undeliveredElementException: UndeliveredElementException? = null // first cancel exception, others suppressed
        state.withLock {
            repeat(state.size) {
                val value = state.getBufferAt(state.head)
                if (onUndeliveredElement != null && value !== EMPTY) {
                    @Suppress("UNCHECKED_CAST")
                    undeliveredElementException = onUndeliveredElement.callUndeliveredElementCatchingException(value as E, undeliveredElementException)
                }
                state.setBufferAt(state.head, null)
                state.head = (state.head + 1) % state.bufferSize
            }
            state.size = 0
        }
        // then clean all queued senders
        super.onCancelIdempotent(wasClosed)
        undeliveredElementException?.let { throw it } // throw UndeliveredElementException at the end if there was one
    }

    // ------ debug ------

    override val bufferDebugString: String
        get() = state.withLock {
            "(buffer:capacity=$capacity,size=${state.size})"
        }
}
