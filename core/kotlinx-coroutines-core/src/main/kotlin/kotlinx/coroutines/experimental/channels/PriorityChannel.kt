/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.selects.ALREADY_SELECTED
import kotlinx.coroutines.experimental.selects.SelectInstance
import java.util.*
import java.util.concurrent.locks.ReentrantLock
import kotlin.concurrent.withLock

/**
 * Channel with priority queue of a fixed [capacity].
 * Sender suspends only when buffer is fully and receiver suspends only when buffer is empty.
 *
 * This channel is created by `Channel(capacity)` factory function invocation.
 *
 * This implementation uses lock to protect the buffer, which is held only during very short buffer-update operations.
 * The lists of suspended senders or receivers are lock-free.
 */
public open class PriorityChannel<E>(
        /**
         * Buffer capacity.
         */
        val capacity: Int
) : AbstractChannel<E>() {
    init {
        require(capacity >= 1) { "PriorityChannel capacity must be at least 1, but $capacity was specified" }
    }

    private val lock = ReentrantLock()
    private val buffer = PriorityQueue<Any>(capacity)

    protected final override val isBufferAlwaysEmpty: Boolean get() = false
    protected final override val isBufferEmpty: Boolean get() = buffer.isEmpty()
    protected final override val isBufferAlwaysFull: Boolean get() = false
    protected final override val isBufferFull: Boolean get() = buffer.size == capacity

    // result is `OFFER_SUCCESS | OFFER_FAILED | Closed`
    protected override fun offerInternal(element: E): Any {
        var receive: ReceiveOrClosed<E>? = null
        var token: Any? = null
        lock.withLock {
            closedForSend?.let { return it }
            if (buffer.size < capacity) {
                // check for receivers that were waiting on empty queue
                if (buffer.isEmpty()) {
                    loop@ while (true) {
                        receive = takeFirstReceiveOrPeekClosed() ?: break@loop // break when no receivers queued
                        if (receive is Closed) {
                            return receive!!
                        }
                        token = receive!!.tryResumeReceive(element, idempotent = null)
                        if (token != null) {
                            return@withLock
                        }
                    }
                }
                buffer.add(element) // actually queue element
                return OFFER_SUCCESS
            }
            // size == capacity: full
            return OFFER_FAILED
        }
        // breaks here if offer meets receiver
        receive!!.completeResumeReceive(token!!)
        return receive!!.offerResult
    }

    // result is `ALREADY_SELECTED | OFFER_SUCCESS | OFFER_FAILED | Closed`
    protected override fun offerSelectInternal(element: E, select: SelectInstance<*>): Any {
        var receive: ReceiveOrClosed<E>? = null
        var token: Any? = null
        lock.withLock {
            closedForSend?.let { return it }
            if (buffer.size < capacity) {
                // check for receivers that were waiting on empty queue
                if (buffer.isEmpty()) {
                    loop@ while (true) {
                        val offerOp = describeTryOffer(element)
                        val failure = select.performAtomicTrySelect(offerOp)
                        when {
                            failure == null -> { // offered successfully
                                receive = offerOp.result
                                token = offerOp.resumeToken
                                check(token != null)
                                return@withLock
                            }
                            failure === OFFER_FAILED -> break@loop // cannot offer -> Ok to queue to buffer
                            failure === ALREADY_SELECTED || failure is Closed<*> -> {
                                return failure
                            }
                            else -> error("performAtomicTrySelect(describeTryOffer) returned $failure")
                        }
                    }
                }
                // let's try to select sending this element to buffer
                if (!select.trySelect(null)) { // :todo: move trySelect completion outside of lock
                    return ALREADY_SELECTED
                }
                buffer.add(element) // actually queue element
                return OFFER_SUCCESS
            }
            // size == capacity: full
            return OFFER_FAILED
        }
        // breaks here if offer meets receiver
        receive!!.completeResumeReceive(token!!)
        return receive!!.offerResult
    }

    // result is `E | POLL_FAILED | Closed`
    protected override fun pollInternal(): Any? {
        var send: Send? = null
        var token: Any? = null
        var result: Any? = lock.withLock {
            if (buffer.isEmpty()){
                return closedForSend ?: POLL_FAILED
            }
            // check for senders that were waiting on full queue
            var replacement: Any? = POLL_FAILED
            if (buffer.size == capacity) {
                loop@ while (true) {
                    send = takeFirstSendOrPeekClosed() ?: break
                    token = send!!.tryResumeSend(idempotent = null)
                    if (token != null) {
                        replacement = send!!.pollResult
                        break@loop
                    }
                }
            }
            if (replacement !== POLL_FAILED && replacement !is Closed<*>) {
                buffer.add(replacement)
            }
            // when nothing can be read from buffer
            // size > 0: not empty -- retrieve element
            buffer.remove()
        }
        // complete send the we're taken replacement from
        if (token != null) {
            send!!.completeResumeSend(token!!)
        }
        return result
    }

    // result is `ALREADY_SELECTED | E | POLL_FAILED | Closed`
    protected override fun pollSelectInternal(select: SelectInstance<*>): Any? {
        var send: Send? = null
        var token: Any? = null
        var result: Any? = null
        lock.withLock {
            if (buffer.isEmpty()) {
                return closedForSend ?: POLL_FAILED
            }
            // check for senders that were waiting on full queue
            var replacement: Any? = POLL_FAILED
            if (buffer.size == capacity) {
                loop@ while (true) {
                    val pollOp = describeTryPoll()
                    val failure = select.performAtomicTrySelect(pollOp)
                    when {
                        failure == null -> { // polled successfully
                            send = pollOp.result
                            token = pollOp.resumeToken
                            check(token != null)
                            replacement = send!!.pollResult
                            break@loop
                        }
                        failure === POLL_FAILED -> break@loop // cannot poll -> Ok to take from buffer
                        failure === ALREADY_SELECTED -> {
                            buffer.add(result) // restore head
                            return failure
                        }
                        failure is Closed<*> -> {
                            send = failure
                            token = failure.tryResumeSend(idempotent = null)
                            replacement = failure
                            break@loop
                        }
                        else -> error("performAtomicTrySelect(describeTryOffer) returned $failure")
                    }
                }
            }
            if (replacement !== POLL_FAILED && replacement !is Closed<*>) {
                buffer.add(replacement)
            }
            // NOTE: Something about the else in ArrayChannel made me do this..
            if ((replacement === POLL_FAILED || replacement is Closed<*>) && !select.trySelect(null)) {
                buffer.add(result) // restore head
                return ALREADY_SELECTED
            }
            // size > 0: not empty -- retrieve element
            result = buffer.remove()
        }
        // complete send the we're taken replacement from
        if (token != null) {
            send!!.completeResumeSend(token!!)
        }
        return result
    }

    // Note: this function is invoked when channel is already closed
    override fun cleanupSendQueueOnCancel() {
        // clear buffer first
        lock.withLock {
            buffer.clear()
        }
        // then clean all queued senders
        super.cleanupSendQueueOnCancel()
    }
}