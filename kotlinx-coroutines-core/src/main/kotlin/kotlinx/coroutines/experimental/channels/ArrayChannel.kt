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

import kotlinx.coroutines.experimental.ALREADY_SELECTED
import kotlinx.coroutines.experimental.selects.SelectInstance
import java.util.concurrent.locks.ReentrantLock

/**
 * Channel with array buffer of a fixed [capacity].
 * Sender suspends only when buffer is fully and receiver suspends only when buffer is empty.
 *
 * This implementation uses lock to protect the buffer, which is held only during very short buffer-update operations.
 * The lists of suspended senders or receivers are lock-free.
 */
public class ArrayChannel<E>(
    /**
     * Buffer capacity.
     */
    val capacity: Int
) : AbstractChannel<E>() {
    init {
        check(capacity >= 1) { "ArrayChannel capacity must be at least 1, but $capacity was specified" }
    }

    private val lock = ReentrantLock()
    private val buffer: Array<Any?> = arrayOfNulls<Any?>(capacity)
    private var head: Int = 0
    @Volatile
    private var size: Int = 0

    private inline fun <T> locked(block: () -> T): T {
        lock.lock()
        return try { block() }
        finally { lock.unlock() }
    }

    override val hasBuffer: Boolean get() = true
    override val isBufferEmpty: Boolean get() = size == 0
    override val isBufferFull: Boolean get() = size == capacity

    // result is `OFFER_SUCCESS | OFFER_FAILED | Closed`
    override fun offerInternal(element: E): Any {
        var receive: ReceiveOrClosed<E>? = null
        var token: Any? = null
        locked {
            val size = this.size
            closedForSend?.let { return it }
            if (size < capacity) {
                // tentatively put element to buffer
                this.size = size + 1 // update size before checking queue (!!!)
                // check for receivers that were waiting on empty queue
                if (size == 0) {
                    loop@ while (true) {
                        receive = takeFirstReceiveOrPeekClosed() ?: break@loop // break when no receivers queued
                        if (receive is Closed) {
                            this.size = size // restore size
                            return receive!!
                        }
                        token = receive!!.tryResumeReceive(element, idempotent = null)
                        if (token != null) {
                            this.size = size // restore size
                            return@locked
                        }
                    }
                }
                buffer[(head + size) % capacity] = element // actually queue element
                return OFFER_SUCCESS
            }
            // size == capacity: full
            return OFFER_FAILED
        }
        // breaks here if offer meets receiver
        receive!!.completeResumeReceive(token!!)
        return receive!!.offerResult
    }

    // result is `ALREADY_SELECTED | OFFER_SUCCESS | OFFER_FAILED | Closed`.
    override fun offerSelectInternal(element: E, select: SelectInstance<*>): Any {
        var receive: ReceiveOrClosed<E>? = null
        var token: Any? = null
        locked {
            val size = this.size
            closedForSend?.let { return it }
            if (size < capacity) {
                // tentatively put element to buffer
                this.size = size + 1 // update size before checking queue (!!!)
                // check for receivers that were waiting on empty queue
                if (size == 0) {
                    loop@ while (true) {
                        val offerOp = describeTryOffer(element)
                        val failure = select.performAtomicTrySelect(offerOp)
                        when {
                            failure == null -> { // offered successfully
                                this.size = size // restore size
                                receive = offerOp.result
                                token = offerOp.resumeToken
                                check(token != null)
                                return@locked
                            }
                            failure === OFFER_FAILED -> break@loop // cannot offer -> Ok to queue to buffer
                            failure === ALREADY_SELECTED || failure is Closed<*> -> {
                                this.size = size // restore size
                                return failure
                            }
                            else -> error("performAtomicTrySelect(describeTryOffer) returned $failure")
                        }
                    }
                }
                // let's try to select sending this element to buffer
                if (!select.trySelect(null)) {
                    this.size = size // restore size
                    return ALREADY_SELECTED
                }
                buffer[(head + size) % capacity] = element // actually queue element
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
    override fun pollInternal(): Any? {
        var send: Send? = null
        var token: Any? = null
        var result: Any? = null
        locked {
            val size = this.size
            if (size == 0) return closedForSend ?: POLL_FAILED
            // size > 0: not empty -- retrieve element
            result = buffer[head]
            buffer[head] = null
            this.size = size - 1 // update size before checking queue (!!!)
            // check for senders that were waiting on full queue
            var replacement: Any? = POLL_FAILED
            if (size == capacity) {
                loop@ while (true) {
                    send = takeFirstSendOrPeekClosed() ?: break
                    token = send!!.tryResumeSend(idempotent = null)
                    if (token != null) {
                        replacement = send!!.pollResult
                        break@loop
                    }
                }
            }
            if (replacement !== POLL_FAILED && !isClosed(replacement)) {
                this.size = size // restore size
                buffer[(head + size) % capacity] = replacement
            }
            head = (head + 1) % capacity
        }
        // complete send the we're taken replacement from
        if (token != null)
            send!!.completeResumeSend(token!!)
        return result
    }

    // result is `ALREADY_SELECTED | E | POLL_FAILED | Closed`
    override fun pollSelectInternal(select: SelectInstance<*>): Any? {
        var send: Send? = null
        var token: Any? = null
        var result: Any? = null
        locked {
            val size = this.size
            if (size == 0) return closedForSend ?: POLL_FAILED
            // size > 0: not empty -- retrieve element
            result = buffer[head]
            buffer[head] = null
            this.size = size - 1 // update size before checking queue (!!!)
            // check for senders that were waiting on full queue
            var replacement: Any? = POLL_FAILED
            if (size == capacity) {
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
                            this.size = size // restore size
                            buffer[head] = result // restore head
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
            if (replacement !== POLL_FAILED && !isClosed(replacement)) {
                this.size = size // restore size
                buffer[(head + size) % capacity] = replacement
            } else {
                // failed to poll or is already closed --> let's try to select receiving this element from buffer
                if (!select.trySelect(null)) {
                    this.size = size // restore size
                    buffer[head] = result // restore head
                    return ALREADY_SELECTED
                }
            }
            head = (head + 1) % capacity
        }
        // complete send the we're taken replacement from
        if (token != null)
            send!!.completeResumeSend(token!!)
        return result
    }
}