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

import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListHead
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListNode
import kotlinx.coroutines.experimental.removeOnCompletion
import kotlinx.coroutines.experimental.suspendCancellableCoroutine

/**
 * Abstract channel. It is a base class for buffered and unbuffered channels.
 */
public abstract class AbstractChannel<E> : Channel<E> {
    private val queue = LockFreeLinkedListHead()

    // ------ extension points for buffered channels ------

    protected abstract val hasBuffer: Boolean
    protected abstract val isBufferEmpty: Boolean
    protected abstract val isBufferFull: Boolean

    /**
     * Tries to add element to buffer or to queued receiver.
     * Return type is `OFFER_SUCCESS | OFFER_FAILED | Closed`.
     */
    protected abstract fun offerInternal(element: E): Any

    /**
     * Tries to remove element from buffer or from queued sender.
     * Return type is `E | POLL_EMPTY | Closed`
     */
    protected abstract fun pollInternal(): Any?


    // ------ state functions for concrete implementations ------

    protected val closedForReceive: Any? get() = queue.next() as? Closed<*>
    protected val closedForSend: Any? get() = queue.prev() as? Closed<*>

    // ------ SendChannel ------

    override val isClosedForSend: Boolean get() = closedForSend != null
    override val isFull: Boolean get() = queue.next() !is ReceiveOrClosed<*> && isBufferFull

    suspend override fun send(element: E) {
        // fast path -- try offer non-blocking
        if (offer(element)) return
        // slow-path does suspend
        return sendSuspend(element)
    }

    override fun offer(element: E): Boolean {
        val result = offerInternal(element)
        return when {
            result === OFFER_SUCCESS -> true
            result is Closed<*> -> throw result.sendException
            else -> false
        }
    }

    private suspend fun sendSuspend(element: E): Unit = suspendCancellableCoroutine(true) sc@ { cont ->
        val send = SendElement(cont, element)
        loop@ while (true) {
            if (enqueueSend(send)) {
                cont.initCancellability() // make it properly cancellable
                cont.removeOnCompletion(send)
                return@sc
            }
            // hm... something is not right. try to offer
            val result = offerInternal(element)
            when {
                result === OFFER_SUCCESS -> {
                    cont.resume(Unit)
                    return@sc
                }
                result is Closed<*> -> {
                    cont.resumeWithException(result.sendException)
                    return@sc
                }
            }
        }
    }

    private fun enqueueSend(send: SendElement) =
        if (hasBuffer)
            queue.addLastIfPrevAndIf(send, { it !is ReceiveOrClosed<*> }, { isBufferFull })
        else
            queue.addLastIfPrev(send, { it !is ReceiveOrClosed<*> })

    override fun close(cause: Throwable?): Boolean {
        val closed = Closed<E>(cause)
        while (true) {
            val receive = takeFirstReceiveOrPeekClosed()
            if (receive == null) {
                // queue empty or has only senders -- try add last "Closed" item to the queue
                if (queue.addLastIfPrev(closed, { it !is ReceiveOrClosed<*> })) return true
                continue // retry on failure
            }
            if (receive is Closed<*>) return false // already marked as closed -- nothing to do
            receive as Receive<E> // type assertion
            receive.resumeReceiveClosed(closed)
        }
    }

    protected fun takeFirstReceiveOrPeekClosed(): ReceiveOrClosed<E>? =
        queue.removeFirstIfIsInstanceOfOrPeekIf<ReceiveOrClosed<E>> { it is Closed<*> }

    // ------ ReceiveChannel ------

    override val isClosedForReceive: Boolean get() = closedForReceive != null && isBufferEmpty
    override val isEmpty: Boolean get() = queue.next() !is Send && isBufferEmpty

    @Suppress("UNCHECKED_CAST")
    suspend override fun receive(): E {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        if (result !== POLL_EMPTY) return receiveResult(result)
        // slow-path does suspend
        return receiveSuspend()
    }

    @Suppress("UNCHECKED_CAST")
    private fun receiveResult(result: Any?): E {
        if (result is Closed<*>) throw result.receiveException
        return result as E
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun receiveSuspend(): E = suspendCancellableCoroutine(true) sc@ { cont ->
        val receive = ReceiveNonNull(cont)
        while (true) {
            if (enqueueReceive(receive)) {
                cont.initCancellability() // make it properly cancellable
                cont.removeOnCompletion(receive)
                return@sc
            }
            // hm... something is not right. try to poll
            val result = pollInternal()
            if (result is Closed<*>) {
                cont.resumeWithException(result.receiveException)
                return@sc
            }
            if (result !== POLL_EMPTY) {
                cont.resume(result as E)
                return@sc
            }
        }
    }

    private fun enqueueReceive(receive: Receive<E>) =
        if (hasBuffer)
            queue.addLastIfPrevAndIf(receive, { it !is Send }, { isBufferEmpty })
        else
            queue.addLastIfPrev(receive, { it !is Send })

    @Suppress("UNCHECKED_CAST")
    suspend override fun receiveOrNull(): E? {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        if (result !== POLL_EMPTY) return receiveOrNullResult(result)
        // slow-path does suspend
        return receiveOrNullSuspend()
    }

    @Suppress("UNCHECKED_CAST")
    private fun receiveOrNullResult(result: Any?): E? {
        if (result is Closed<*>) {
            if (result.closeCause != null) throw result.receiveException
            return null
        }
        return result as E
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun receiveOrNullSuspend(): E? = suspendCancellableCoroutine(true) sc@ { cont ->
        val receive = ReceiveOrNull(cont)
        while (true) {
            if (enqueueReceive(receive)) {
                cont.initCancellability() // make it properly cancellable
                cont.removeOnCompletion(receive)
                return@sc
            }
            // hm... something is not right. try to poll
            val result = pollInternal()
            if (result is Closed<*>) {
                if (result.closeCause == null)
                    cont.resume(null)
                else
                    cont.resumeWithException(result.receiveException)
                return@sc
            }
            if (result !== POLL_EMPTY) {
                cont.resume(result as E)
                return@sc
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    override fun poll(): E? {
        val result = pollInternal()
        return if (result === POLL_EMPTY) null else receiveOrNullResult(result)
    }

    override fun iterator(): ChannelIterator<E> = Iterator(this)

    protected fun takeFirstSendOrPeekClosed(): Send? =
        queue.removeFirstIfIsInstanceOfOrPeekIf<Send> { it is Closed<*> }

    protected companion object {
        const val DEFAULT_CLOSE_MESSAGE = "Channel was closed"

        val OFFER_SUCCESS: Any = Marker("OFFER_SUCCESS")
        val OFFER_FAILED: Any = Marker("OFFER_FAILED")

        val POLL_EMPTY: Any = Marker("POLL_EMPTY")

        fun isClosed(result: Any?): Boolean = result is Closed<*>
    }

    // for debugging
    private class Marker(val string: String) {
        override fun toString(): String = string
    }

    private class Iterator<E>(val channel: AbstractChannel<E>) : ChannelIterator<E> {
        var result: Any? = POLL_EMPTY // E | POLL_CLOSED | POLL_EMPTY

        suspend override fun hasNext(): Boolean {
            // check for repeated hasNext
            if (result !== POLL_EMPTY) return hasNextResult(result)
            // fast path -- try poll non-blocking
            result = channel.pollInternal()
            if (result !== POLL_EMPTY) return hasNextResult(result)
            // slow-path does suspend
            return hasNextSuspend()
        }

        private fun hasNextResult(result: Any?): Boolean {
            if (result is Closed<*>) {
                if (result.closeCause != null) throw result.receiveException
                return false
            }
            return true
        }

        private suspend fun hasNextSuspend(): Boolean = suspendCancellableCoroutine(true) sc@ { cont ->
            val receive = ReceiveHasNext(this, cont)
            while (true) {
                if (channel.enqueueReceive(receive)) {
                    cont.initCancellability() // make it properly cancellable
                    cont.removeOnCompletion(receive)
                    return@sc
                }
                // hm... something is not right. try to poll
                val result = channel.pollInternal()
                this.result = result
                if (result is Closed<*>) {
                    if (result.closeCause == null)
                        cont.resume(false)
                    else
                        cont.resumeWithException(result.receiveException)
                    return@sc
                }
                if (result !== POLL_EMPTY) {
                    cont.resume(true)
                    return@sc
                }
            }
        }

        @Suppress("UNCHECKED_CAST")
        suspend override fun next(): E {
            val result = this.result
            if (result is Closed<*>) throw result.receiveException
            if (result !== POLL_EMPTY) {
                this.result = POLL_EMPTY
                return result as E
            }
            // rare case when hasNext was not invoked yet -- just delegate to receive (leave state as is)
            return channel.receive()
        }
    }

    protected interface Send {
        val pollResult: Any? // E | Closed
        fun tryResumeSend(): Any?
        fun completeResumeSend(token: Any)
    }

    protected interface ReceiveOrClosed<in E> {
        val offerResult: Any // OFFER_SUCCESS | Closed
        fun tryResumeReceive(value: E): Any?
        fun completeResumeReceive(token: Any)
    }

    @Suppress("UNCHECKED_CAST")
    private class SendElement(
            val cont: CancellableContinuation<Unit>,
            override val pollResult: Any?
    ) : LockFreeLinkedListNode(), Send {
        override fun tryResumeSend(): Any? = cont.tryResume(Unit)
        override fun completeResumeSend(token: Any) = cont.completeResume(token)
    }

    private class Closed<in E>(
        val closeCause: Throwable?
    ) : LockFreeLinkedListNode(), Send, ReceiveOrClosed<E> {
        @Volatile
        var _sendException: Throwable? = null

        val sendException: Throwable get() = _sendException ?:
            (closeCause ?: ClosedSendChannelException(DEFAULT_CLOSE_MESSAGE))
                    .also { _sendException = it }

        @Volatile
        var _receiveException: Throwable? = null

        val receiveException: Throwable get() = _receiveException ?:
            (closeCause ?: ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE))
                    .also { _receiveException = it }

        override val offerResult get() = this
        override val pollResult get() = this
        override fun tryResumeSend(): Boolean = true
        override fun completeResumeSend(token: Any) {}
        override fun tryResumeReceive(value: E): Any? = throw sendException
        override fun completeResumeReceive(token: Any) = throw sendException
    }

    private abstract class Receive<in E> : LockFreeLinkedListNode(), ReceiveOrClosed<E> {
        override val offerResult get() = OFFER_SUCCESS
        abstract fun resumeReceiveClosed(closed: Closed<*>)
    }

    private class ReceiveNonNull<in E>(val cont: CancellableContinuation<E>) : Receive<E>() {
        override fun tryResumeReceive(value: E): Any? = cont.tryResume(value)
        override fun completeResumeReceive(token: Any) = cont.completeResume(token)
        override fun resumeReceiveClosed(closed: Closed<*>) = cont.resumeWithException(closed.receiveException)
    }

    private class ReceiveOrNull<in E>(val cont: CancellableContinuation<E?>) : Receive<E>() {
        override fun tryResumeReceive(value: E): Any? = cont.tryResume(value)
        override fun completeResumeReceive(token: Any) = cont.completeResume(token)
        override fun resumeReceiveClosed(closed: Closed<*>) {
            if (closed.closeCause == null)
                cont.resume(null)
            else
                cont.resumeWithException(closed.receiveException)
        }
    }

    private class ReceiveHasNext<E>(
            val iterator: Iterator<E>,
            val cont: CancellableContinuation<Boolean>
    ) : Receive<E>() {
        override fun tryResumeReceive(value: E): Any? {
            val token = cont.tryResume(true)
            if (token != null) iterator.result = value
            return token
        }

        override fun completeResumeReceive(token: Any) = cont.completeResume(token)

        override fun resumeReceiveClosed(closed: Closed<*>) {
            val token = if (closed.closeCause == null)
                cont.tryResume(false)
            else
                cont.tryResumeWithException(closed.receiveException)
            if (token != null) {
                iterator.result = closed
                cont.completeResume(token)
            }
        }
    }
}
