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

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.internal.*
import kotlinx.coroutines.experimental.intrinsics.startUndispatchedCoroutine
import kotlinx.coroutines.experimental.selects.SelectInstance
import kotlin.coroutines.experimental.startCoroutine

/**
 * Abstract channel. It is a base class for all channel implementations.
 */
public abstract class AbstractChannel<E> : Channel<E> {
    private val queue = LockFreeLinkedListHead()

    // ------ extension points for buffered channels ------

    /**
     * Returns `true` if [isBufferEmpty] is always `true`.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected abstract val isBufferAlwaysEmpty: Boolean

    /**
     * Returns `true` if this channel's buffer is empty.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected abstract val isBufferEmpty: Boolean

    /**
     * Returns `true` if [isBufferFull] is always `true`.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected abstract val isBufferAlwaysFull: Boolean

    /**
     * Returns `true` if this channel's buffer is full.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected abstract val isBufferFull: Boolean

    // ------ internal functions for override by buffered channels ------

    /**
     * Tries to add element to buffer or to queued receiver.
     * Return type is `OFFER_SUCCESS | OFFER_FAILED | Closed`.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun offerInternal(element: E): Any {
        while (true) {
            val receive = takeFirstReceiveOrPeekClosed() ?: return OFFER_FAILED
            val token = receive.tryResumeReceive(element, idempotent = null)
            if (token != null) {
                receive.completeResumeReceive(token)
                return receive.offerResult
            }
        }
    }

    /**
     * Tries to add element to buffer or to queued receiver if select statement clause was not selected yet.
     * Return type is `ALREADY_SELECTED | OFFER_SUCCESS | OFFER_FAILED | Closed`.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun offerSelectInternal(element: E, select: SelectInstance<*>): Any {
        // offer atomically with select
        val offerOp = describeTryOffer(element)
        val failure = select.performAtomicTrySelect(offerOp)
        if (failure != null) return failure
        val receive = offerOp.result
        receive.completeResumeReceive(offerOp.resumeToken!!)
        return receive.offerResult
    }

    /**
     * Tries to remove element from buffer or from queued sender.
     * Return type is `E | POLL_FAILED | Closed`
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun pollInternal(): Any? {
        while (true) {
            val send = takeFirstSendOrPeekClosed() ?: return POLL_FAILED
            val token = send.tryResumeSend(idempotent = null)
            if (token != null) {
                send.completeResumeSend(token)
                return send.pollResult
            }
        }
    }

    /**
     * Tries to remove element from buffer or from queued sender if select statement clause was not selected yet.
     * Return type is `ALREADY_SELECTED | E | POLL_FAILED | Closed`
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun pollSelectInternal(select: SelectInstance<*>): Any? {
        // poll atomically with select
        val pollOp = describeTryPoll()
        val failure = select.performAtomicTrySelect(pollOp)
        if (failure != null) return failure
        val send = pollOp.result
        send.completeResumeSend(pollOp.resumeToken!!)
        return pollOp.pollResult
    }

    // ------ state functions & helpers for concrete implementations ------

    /**
     * Returns non-null closed token if it is first in the queue.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected val closedForReceive: Any? get() = queue.next as? Closed<*>

    /**
     * Returns non-null closed token if it is last in the queue.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected val closedForSend: ReceiveOrClosed<*>? get() = queue.prev as? Closed<*>

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected val hasReceiveOrClosed: Boolean get() = queue.next is ReceiveOrClosed<*>

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun sendBuffered(element: E): Boolean =
        queue.addLastIfPrev(SendBuffered(element), { it !is ReceiveOrClosed<*> })

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun sendConflated(element: E): Boolean {
        val node = SendBuffered(element)
        if (!queue.addLastIfPrev(node, { it !is ReceiveOrClosed<*> })) return false
        // remove previous SendBuffered
        val prev = node.prev
        if (prev is SendBuffered<*>)
            prev.remove()
        return true
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun describeSendBuffered(element: E): AddLastDesc<*> = SendBufferedDesc(queue, element)

    private open class SendBufferedDesc<out E>(
        queue: LockFreeLinkedListHead,
        element: E
    ) : AddLastDesc<SendBuffered<E>>(queue, SendBuffered(element)) {
        override fun failure(affected: LockFreeLinkedListNode, next: Any): Any? {
            if (affected is ReceiveOrClosed<*>) return OFFER_FAILED
            return null
        }
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun describeSendConflated(element: E): AddLastDesc<*> = SendConflatedDesc(queue, element)

    private class SendConflatedDesc<out E>(
        queue: LockFreeLinkedListHead,
        element: E
    ) : SendBufferedDesc<E>(queue, element) {
        override fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode) {
            super.finishOnSuccess(affected, next)
            // remove previous SendBuffered
            if (affected is SendBuffered<*>)
                affected.remove()
        }
    }

    // ------ SendChannel ------

    public final override val isClosedForSend: Boolean get() = closedForSend != null
    public final override val isFull: Boolean get() = queue.next !is ReceiveOrClosed<*> && isBufferFull

    public final override suspend fun send(element: E) {
        // fast path -- try offer non-blocking
        if (offer(element)) return
        // slow-path does suspend
        return sendSuspend(element)
    }

    public final override fun offer(element: E): Boolean {
        val result = offerInternal(element)
        return when {
            result === OFFER_SUCCESS -> true
            result === OFFER_FAILED -> false
            result is Closed<*> -> throw result.sendException
            else -> error("offerInternal returned $result")
        }
    }

    private suspend fun sendSuspend(element: E): Unit = suspendCancellableCoroutine(true) sc@ { cont ->
        val send = SendElement(element, cont)
        loop@ while (true) {
            if (enqueueSend(send)) {
                cont.initCancellability() // make it properly cancellable
                cont.removeOnCancel(send)
                return@sc
            }
            // hm... something is not right. try to offer
            val result = offerInternal(element)
            when {
                result === OFFER_SUCCESS -> {
                    cont.resume(Unit)
                    return@sc
                }
                result === OFFER_FAILED -> continue@loop
                result is Closed<*> -> {
                    cont.resumeWithException(result.sendException)
                    return@sc
                }
                else -> error("offerInternal returned $result")
            }
        }
    }

    private fun enqueueSend(send: SendElement) =
        if (isBufferAlwaysFull)
            queue.addLastIfPrev(send, { it !is ReceiveOrClosed<*> }) else
            queue.addLastIfPrevAndIf(send, { it !is ReceiveOrClosed<*> }, { isBufferFull })

    public final override fun close(cause: Throwable?): Boolean {
        val closed = Closed<E>(cause)
        while (true) {
            val receive = takeFirstReceiveOrPeekClosed()
            if (receive == null) {
                // queue empty or has only senders -- try add last "Closed" item to the queue
                if (queue.addLastIfPrev(closed, { it !is ReceiveOrClosed<*> })) {
                    afterClose(cause)
                    return true
                }
                continue // retry on failure
            }
            if (receive is Closed<*>) return false // already marked as closed -- nothing to do
            receive as Receive<E> // type assertion
            receive.resumeReceiveClosed(closed)
        }
    }

    /**
     * Invoked after successful [close].
     */
    protected open fun afterClose(cause: Throwable?) {}

    /**
     * Retrieves first receiving waiter from the queue or returns closed token.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun takeFirstReceiveOrPeekClosed(): ReceiveOrClosed<E>? =
        queue.removeFirstIfIsInstanceOfOrPeekIf<ReceiveOrClosed<E>>({ it is Closed<*> })

    // ------ registerSelectSend ------

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun describeTryOffer(element: E): TryOfferDesc<E> = TryOfferDesc(element, queue)

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected class TryOfferDesc<E>(
        @JvmField val element: E,
        queue: LockFreeLinkedListHead
    ) : RemoveFirstDesc<ReceiveOrClosed<E>>(queue) {
        @JvmField var resumeToken: Any? = null

        override fun failure(affected: LockFreeLinkedListNode, next: Any): Any? {
            if (affected !is ReceiveOrClosed<*>) return OFFER_FAILED
            if (affected is Closed<*>) return affected
            return null
        }

        override fun validatePrepared(node: ReceiveOrClosed<E>): Boolean {
            val token = node.tryResumeReceive(element, idempotent = this) ?: return false
            resumeToken = token
            return true
        }
    }

    private inner class TryEnqueueSendDesc<E, R>(
        element: E,
        select: SelectInstance<R>,
        block: suspend () -> R
    ) : AddLastDesc<SendSelect<R>>(queue, SendSelect(element, select, block)) {
        override fun failure(affected: LockFreeLinkedListNode, next: Any): Any? {
            if (affected is ReceiveOrClosed<*>) {
                return affected as? Closed<*> ?: ENQUEUE_FAILED
            }
            return null
        }

        override fun onPrepare(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode): Any? {
            if (!isBufferFull) return ENQUEUE_FAILED
            return super.onPrepare(affected, next)
        }

        override fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode) {
            super.finishOnSuccess(affected, next)
            // we can actually remove on select start, but this is also Ok (it'll get removed if discovered there)
            node.disposeOnSelect()
        }
    }

    override fun <R> registerSelectSend(select: SelectInstance<R>, element: E, block: suspend () -> R) {
        while (true) {
            if (select.isSelected) return
            if (isFull) {
                val enqueueOp = TryEnqueueSendDesc(element, select, block)
                val enqueueResult = select.performAtomicIfNotSelected(enqueueOp) ?: return
                when {
                    enqueueResult === ALREADY_SELECTED -> return
                    enqueueResult === ENQUEUE_FAILED -> {} // retry
                    enqueueResult is Closed<*> -> throw enqueueResult.sendException
                    else -> error("performAtomicIfNotSelected(TryEnqueueSendDesc) returned $enqueueResult")
                }
            } else {
                val offerResult = offerSelectInternal(element, select)
                when {
                    offerResult === ALREADY_SELECTED -> return
                    offerResult === OFFER_FAILED -> {} // retry
                    offerResult === OFFER_SUCCESS -> {
                        block.startUndispatchedCoroutine(select.completion)
                        return
                    }
                    offerResult is Closed<*> -> throw offerResult.sendException
                    else -> error("offerSelectInternal returned $offerResult")
                }
            }
        }
    }

    // ------ ReceiveChannel ------

    public final override val isClosedForReceive: Boolean get() = closedForReceive != null && isBufferEmpty
    public final override val isEmpty: Boolean get() = queue.next !is Send && isBufferEmpty

    @Suppress("UNCHECKED_CAST")
    public final override suspend fun receive(): E {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        if (result !== POLL_FAILED) return receiveResult(result)
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
        val receive = ReceiveElement(cont as CancellableContinuation<E?>, nullOnClose = false)
        while (true) {
            if (enqueueReceive(receive)) {
                cont.initCancellability() // make it properly cancellable
                removeReceiveOnCancel(cont, receive)
                return@sc
            }
            // hm... something is not right. try to poll
            val result = pollInternal()
            if (result is Closed<*>) {
                cont.resumeWithException(result.receiveException)
                return@sc
            }
            if (result !== POLL_FAILED) {
                cont.resume(result as E)
                return@sc
            }
        }
    }

    private fun enqueueReceive(receive: Receive<E>): Boolean {
        val result = if (isBufferAlwaysEmpty)
            queue.addLastIfPrev(receive, { it !is Send }) else
            queue.addLastIfPrevAndIf(receive, { it !is Send }, { isBufferEmpty })
        if (result) onEnqueuedReceive()
        return result
    }

    @Suppress("UNCHECKED_CAST")
    public final override suspend fun receiveOrNull(): E? {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        if (result !== POLL_FAILED) return receiveOrNullResult(result)
        // slow-path does suspend
        return receiveOrNullSuspend()
    }

    @Suppress("UNCHECKED_CAST")
    private fun receiveOrNullResult(result: Any?): E? {
        if (result is Closed<*>) {
            if (result.closeCause != null) throw result.closeCause
            return null
        }
        return result as E
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun receiveOrNullSuspend(): E? = suspendCancellableCoroutine(true) sc@ { cont ->
        val receive = ReceiveElement(cont, nullOnClose = true)
        while (true) {
            if (enqueueReceive(receive)) {
                cont.initCancellability() // make it properly cancellable
                removeReceiveOnCancel(cont, receive)
                return@sc
            }
            // hm... something is not right. try to poll
            val result = pollInternal()
            if (result is Closed<*>) {
                if (result.closeCause == null)
                    cont.resume(null)
                else
                    cont.resumeWithException(result.closeCause)
                return@sc
            }
            if (result !== POLL_FAILED) {
                cont.resume(result as E)
                return@sc
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    public final override fun poll(): E? {
        val result = pollInternal()
        return if (result === POLL_FAILED) null else receiveOrNullResult(result)
    }

    public final override fun iterator(): ChannelIterator<E> = Iterator(this)

    /**
     * Retrieves first sending waiter from the queue or returns closed token.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun takeFirstSendOrPeekClosed(): Send? =
        queue.removeFirstIfIsInstanceOfOrPeekIf<Send> { it is Closed<*> }

    // ------ registerSelectReceive ------

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun describeTryPoll(): TryPollDesc<E> = TryPollDesc(queue)

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected class TryPollDesc<E>(queue: LockFreeLinkedListHead) : RemoveFirstDesc<Send>(queue) {
        @JvmField var resumeToken: Any? = null
        @JvmField var pollResult: E? = null

        override fun failure(affected: LockFreeLinkedListNode, next: Any): Any? {
            if (affected is Closed<*>) return affected
            if (affected !is Send) return POLL_FAILED
            return null
        }

        @Suppress("UNCHECKED_CAST")
        override fun validatePrepared(node: Send): Boolean {
            val token = node.tryResumeSend(this) ?: return false
            resumeToken = token
            pollResult = node.pollResult as E
            return true
        }
    }

    private inner class TryEnqueueReceiveDesc<in E, R>(
        select: SelectInstance<R>,
        block: suspend (E?) -> R,
        nullOnClose: Boolean
    ) : AddLastDesc<ReceiveSelect<R, E>>(queue, ReceiveSelect(select, block, nullOnClose)) {
        override fun failure(affected: LockFreeLinkedListNode, next: Any): Any? {
            if (affected is Send) return ENQUEUE_FAILED
            return null
        }

        override fun onPrepare(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode): Any? {
            if (!isBufferEmpty) return ENQUEUE_FAILED
            return super.onPrepare(affected, next)
        }

        override fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode) {
            super.finishOnSuccess(affected, next)
            // notify the there is one more receiver
            onEnqueuedReceive()
            // we can actually remove on select start, but this is also Ok (it'll get removed if discovered there)
            node.removeOnSelectCompletion()
        }
    }

    @Suppress("UNCHECKED_CAST")
    override fun <R> registerSelectReceive(select: SelectInstance<R>, block: suspend (E) -> R) {
        while (true) {
            if (select.isSelected) return
            if (isEmpty) {
                val enqueueOp = TryEnqueueReceiveDesc(select, block as (suspend (E?) -> R), nullOnClose = false)
                val enqueueResult = select.performAtomicIfNotSelected(enqueueOp) ?: return
                when {
                    enqueueResult === ALREADY_SELECTED -> return
                    enqueueResult === ENQUEUE_FAILED -> {} // retry
                    else -> error("performAtomicIfNotSelected(TryEnqueueReceiveDesc) returned $enqueueResult")
                }
            } else {
                val pollResult = pollSelectInternal(select)
                when {
                    pollResult === ALREADY_SELECTED -> return
                    pollResult === POLL_FAILED -> {} // retry
                    pollResult is Closed<*> -> throw pollResult.receiveException
                    else -> {
                        block.startUndispatchedCoroutine(pollResult as E, select.completion)
                        return
                    }
                }
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    override fun <R> registerSelectReceiveOrNull(select: SelectInstance<R>, block: suspend (E?) -> R) {
        while (true) {
            if (select.isSelected) return
            if (isEmpty) {
                val enqueueOp = TryEnqueueReceiveDesc(select, block, nullOnClose = true)
                val enqueueResult = select.performAtomicIfNotSelected(enqueueOp) ?: return
                when {
                    enqueueResult === ALREADY_SELECTED -> return
                    enqueueResult === ENQUEUE_FAILED -> {} // retry
                    else -> error("performAtomicIfNotSelected(TryEnqueueReceiveDesc) returned $enqueueResult")
                }
            } else {
                val pollResult = pollSelectInternal(select)
                when {
                    pollResult === ALREADY_SELECTED -> return
                    pollResult === POLL_FAILED -> {} // retry
                    pollResult is Closed<*> -> {
                        if (pollResult.closeCause == null) {
                            if (select.trySelect(idempotent = null))
                                block.startUndispatchedCoroutine(null, select.completion)
                            return
                        } else
                            throw pollResult.closeCause
                    }
                    else -> {
                        // selected successfully
                        block.startUndispatchedCoroutine(pollResult as E, select.completion)
                        return
                    }
                }
            }
        }
    }

    // ------ protected ------

    protected companion object {
        private const val DEFAULT_CLOSE_MESSAGE = "Channel was closed"

        /** @suppress **This is unstable API and it is subject to change.** */
        @JvmStatic
        val OFFER_SUCCESS: Any = Symbol("OFFER_SUCCESS")

        /** @suppress **This is unstable API and it is subject to change.** */
        @JvmStatic
        val OFFER_FAILED: Any = Symbol("OFFER_FAILED")

        /** @suppress **This is unstable API and it is subject to change.** */
        @JvmStatic
        val POLL_FAILED: Any = Symbol("POLL_FAILED")

        /** @suppress **This is unstable API and it is subject to change.** */
        @JvmStatic
        val ENQUEUE_FAILED: Any = Symbol("ENQUEUE_FAILED")

        @JvmStatic
        private val SELECT_STARTED: Any = Symbol("SELECT_STARTED")

        @JvmStatic
        private val NULL_VALUE: Any = Symbol("NULL_VALUE")

        @JvmStatic
        private val CLOSE_RESUMED: Any = Symbol("CLOSE_RESUMED")

        @JvmStatic
        private val SEND_RESUMED = Symbol("SEND_RESUMED")

        /** @suppress **This is unstable API and it is subject to change.** */
        @JvmStatic
        fun isClosed(result: Any?): Boolean = result is Closed<*>
    }

    /**
     * Invoked when receiver is successfully enqueued to the queue of waiting receivers.
     */
    protected open fun onEnqueuedReceive() {}

    /**
     * Invoked when enqueued receiver was successfully cancelled.
     */
    protected open fun onCancelledReceive() {}

    // ------ private ------

    private fun removeReceiveOnCancel(cont: CancellableContinuation<*>, receive: Receive<*>) {
        cont.invokeOnCompletion {
            if (cont.isCancelled && receive.remove())
                onCancelledReceive()
        }
    }

    private class Iterator<E>(val channel: AbstractChannel<E>) : ChannelIterator<E> {
        var result: Any? = POLL_FAILED // E | POLL_FAILED | Closed

        suspend override fun hasNext(): Boolean {
            // check for repeated hasNext
            if (result !== POLL_FAILED) return hasNextResult(result)
            // fast path -- try poll non-blocking
            result = channel.pollInternal()
            if (result !== POLL_FAILED) return hasNextResult(result)
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
                    channel.removeReceiveOnCancel(cont, receive)
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
                if (result !== POLL_FAILED) {
                    cont.resume(true)
                    return@sc
                }
            }
        }

        @Suppress("UNCHECKED_CAST")
        suspend override fun next(): E {
            val result = this.result
            if (result is Closed<*>) throw result.receiveException
            if (result !== POLL_FAILED) {
                this.result = POLL_FAILED
                return result as E
            }
            // rare case when hasNext was not invoked yet -- just delegate to receive (leave state as is)
            return channel.receive()
        }
    }

    /**
     * Represents sending waiter in the queue.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected interface Send {
        val pollResult: Any? // E | Closed
        fun tryResumeSend(idempotent: Any?): Any?
        fun completeResumeSend(token: Any)
    }

    /**
     * Represents receiver waiter in the queue or closed token.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected interface ReceiveOrClosed<in E> {
        val offerResult: Any // OFFER_SUCCESS | Closed
        fun tryResumeReceive(value: E, idempotent: Any?): Any?
        fun completeResumeReceive(token: Any)
    }

    @Suppress("UNCHECKED_CAST")
    private class SendElement(
        override val pollResult: Any?,
        @JvmField val cont: CancellableContinuation<Unit>
    ) : LockFreeLinkedListNode(), Send {
        override fun tryResumeSend(idempotent: Any?): Any? = cont.tryResume(Unit, idempotent)
        override fun completeResumeSend(token: Any) = cont.completeResume(token)
        override fun toString(): String = "SendElement($pollResult)[$cont]"
    }

    private class SendSelect<R>(
        override val pollResult: Any?,
        @JvmField val select: SelectInstance<R>,
        @JvmField val block: suspend () -> R
    ) : LockFreeLinkedListNode(), Send, DisposableHandle {
        override fun tryResumeSend(idempotent: Any?): Any? =
            if (select.trySelect(idempotent)) SELECT_STARTED else null

        override fun completeResumeSend(token: Any) {
            check(token === SELECT_STARTED)
            block.startCoroutine(select.completion)
        }

        fun disposeOnSelect() {
            select.disposeOnSelect(this)
        }

        override fun dispose() {
            remove()
        }

        override fun toString(): String = "SendSelect($pollResult)[$select]"
    }

    private class SendBuffered<out E>(
        @JvmField val element: E
    ) : LockFreeLinkedListNode(), Send {
        override val pollResult: Any? get() = element
        override fun tryResumeSend(idempotent: Any?): Any? = SEND_RESUMED
        override fun completeResumeSend(token: Any) { check(token === SEND_RESUMED) }
    }

    /**
     * Represents closed channel.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected class Closed<in E>(
        @JvmField val closeCause: Throwable?
    ) : LockFreeLinkedListNode(), Send, ReceiveOrClosed<E> {
        @Volatile
        private var _sendException: Throwable? = null

        val sendException: Throwable get() = _sendException ?:
            (closeCause ?: ClosedSendChannelException(DEFAULT_CLOSE_MESSAGE))
                    .also { _sendException = it }

        @Volatile
        private var _receiveException: Throwable? = null

        val receiveException: Throwable get() = _receiveException ?:
            (closeCause ?: ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE))
                    .also { _receiveException = it }

        override val offerResult get() = this
        override val pollResult get() = this
        override fun tryResumeSend(idempotent: Any?): Any? = CLOSE_RESUMED
        override fun completeResumeSend(token: Any) { check(token === CLOSE_RESUMED) }
        override fun tryResumeReceive(value: E, idempotent: Any?): Any? = throw sendException
        override fun completeResumeReceive(token: Any) = throw sendException
        override fun toString(): String = "Closed[$closeCause]"
    }

    private abstract class Receive<in E> : LockFreeLinkedListNode(), ReceiveOrClosed<E> {
        override val offerResult get() = OFFER_SUCCESS
        abstract fun resumeReceiveClosed(closed: Closed<*>)
    }

    private class ReceiveElement<in E>(
        @JvmField val cont: CancellableContinuation<E?>,
        @JvmField val nullOnClose: Boolean
    ) : Receive<E>() {
        override fun tryResumeReceive(value: E, idempotent: Any?): Any? = cont.tryResume(value, idempotent)
        override fun completeResumeReceive(token: Any) = cont.completeResume(token)
        override fun resumeReceiveClosed(closed: Closed<*>) {
            if (closed.closeCause == null && nullOnClose)
                cont.resume(null)
            else
                cont.resumeWithException(closed.receiveException)
        }
        override fun toString(): String = "ReceiveElement[$cont,nullOnClose=$nullOnClose]"
    }

    private class IdempotentTokenValue<out E>(
        @JvmField val token: Any,
        @JvmField val value: E
    )

    private class ReceiveHasNext<E>(
        @JvmField val iterator: Iterator<E>,
        @JvmField val cont: CancellableContinuation<Boolean>
    ) : Receive<E>() {
        override fun tryResumeReceive(value: E, idempotent: Any?): Any? {
            val token = cont.tryResume(true, idempotent)
            if (token != null) {
                /*
                   When idempotent != null this invocation can be stale and we cannot directly update iterator.result
                   Instead, we save both token & result into a temporary IdempotentTokenValue object and
                   set iterator result only in completeResumeReceive that is going to be invoked just once
                 */
                if (idempotent != null) return IdempotentTokenValue(token, value)
                iterator.result = value
            }
            return token
        }

        override fun completeResumeReceive(token: Any) {
            if (token is IdempotentTokenValue<*>) {
                iterator.result = token.value
                cont.completeResume(token.token)
            } else
                cont.completeResume(token)
        }

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
        override fun toString(): String = "ReceiveHasNext[$cont]"
    }

    private inner class ReceiveSelect<R, in E>(
        @JvmField val select: SelectInstance<R>,
        @JvmField val block: suspend (E?) -> R,
        @JvmField val nullOnClose: Boolean
    ) : Receive<E>(), DisposableHandle {
        override fun tryResumeReceive(value: E, idempotent: Any?): Any?  =
            if (select.trySelect(idempotent)) (value ?: NULL_VALUE) else null

        @Suppress("UNCHECKED_CAST")
        override fun completeResumeReceive(token: Any) {
            val value: E = (if (token === NULL_VALUE) null else token) as E
            block.startCoroutine(value, select.completion)
        }

        override fun resumeReceiveClosed(closed: Closed<*>) {
            if (select.trySelect(idempotent = null)) {
                if (closed.closeCause == null && nullOnClose) {
                    block.startCoroutine(null, select.completion)
                } else
                    select.resumeSelectWithException(closed.receiveException, MODE_DISPATCHED)
            }
        }

        fun removeOnSelectCompletion() {
            select.disposeOnSelect(this)
        }

        override fun dispose() { // invoked on select completion
            if (remove())
                onCancelledReceive() // notify cancellation of receive
        }

        override fun toString(): String = "ReceiveSelect[$select,nullOnClose=$nullOnClose]"
    }
}
