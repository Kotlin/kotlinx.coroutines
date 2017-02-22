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

import kotlinx.coroutines.experimental.selects.SelectInstance

/**
 * Rendezvous channel. This channel does not have any buffer at all. An element is transferred from sender
 * to receiver only when [send] and [receive] invocations meet in time (rendezvous), so [send] suspends
 * until another coroutine invokes [receive] and [receive] suspends until another coroutine invokes [send].
 *
 * This implementation is fully lock-free.
 */
public open class RendezvousChannel<E> : AbstractChannel<E>() {

    protected final override val hasBuffer: Boolean get() = false
    protected final override val isBufferEmpty: Boolean get() = true
    protected final override val isBufferFull: Boolean get() = true

    // result is `OFFER_SUCCESS | OFFER_FAILED | Closed`
    protected final override fun offerInternal(element: E): Any {
        while (true) {
            val receive = takeFirstReceiveOrPeekClosed() ?: return OFFER_FAILED
            val token = receive.tryResumeReceive(element, idempotent = null)
            if (token != null) {
                receive.completeResumeReceive(token)
                return receive.offerResult
            }
        }
    }

    // result is `ALREADY_SELECTED | OFFER_SUCCESS | OFFER_FAILED | Closed`.
    protected final override fun offerSelectInternal(element: E, select: SelectInstance<*>): Any {
        // offer atomically with select
        val offerOp = describeTryOffer(element)
        val failure = select.performAtomicTrySelect(offerOp)
        if (failure != null) return failure
        val receive = offerOp.result
        receive.completeResumeReceive(offerOp.resumeToken!!)
        return receive.offerResult
    }

    // result is `E | POLL_FAILED | Closed`
    protected final override fun pollInternal(): Any? {
        while (true) {
            val send = takeFirstSendOrPeekClosed() ?: return POLL_FAILED
            val token = send.tryResumeSend(idempotent = null)
            if (token != null) {
                send.completeResumeSend(token)
                return send.pollResult
            }
        }
    }

    // result is `ALREADY_SELECTED | E | POLL_FAILED | Closed`
    protected override fun pollSelectInternal(select: SelectInstance<*>): Any? {
        // poll atomically with select
        val pollOp = describeTryPoll()
        val failure = select.performAtomicTrySelect(pollOp)
        if (failure != null) return failure
        val send = pollOp.result
        send.completeResumeSend(pollOp.resumeToken!!)
        return pollOp.pollResult
    }
}

