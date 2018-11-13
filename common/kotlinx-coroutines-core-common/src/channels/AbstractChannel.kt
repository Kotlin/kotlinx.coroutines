/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * Abstract send channel. It is a base class for all send channel implementations.
 *
 */
internal abstract class AbstractSendChannel<E> : SendChannel<E> {
    /** @suppress **This is unstable API and it is subject to change.** */
    protected val queue = LockFreeLinkedListHead()

    // ------ extension points for buffered channels ------

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

    // State transitions: null -> handler -> HANDLER_INVOKED
    private val onCloseHandler = atomic<Any?>(null)

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

    // ------ state functions & helpers for concrete implementations ------

    /**
     * Returns non-null closed token if it is last in the queue.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected val closedForSend: Closed<*>? get() = (queue.prevNode as? Closed<*>)?.also { helpClose(it) }

    /**
     * Returns non-null closed token if it is first in the queue.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected val closedForReceive: Closed<*>? get() = (queue.nextNode as? Closed<*>)?.also { helpClose(it) }

    /**
     * Retrieves first sending waiter from the queue or returns closed token.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun takeFirstSendOrPeekClosed(): Send? =
        queue.removeFirstIfIsInstanceOfOrPeekIf<Send> { it is Closed<*> }

    /**
     * Queues buffered element, returns null on success or
     * returns node reference if it was already closed or is waiting for receive.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun sendBuffered(element: E): ReceiveOrClosed<*>? {
        queue.addLastIfPrev(SendBuffered(element), { prev ->
            if (prev is ReceiveOrClosed<*>) return@sendBuffered prev
            true
        })
        return null
    }

    /**
     * Queues conflated element, returns null on success or
     * returns node reference if it was already closed or is waiting for receive.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun sendConflated(element: E): ReceiveOrClosed<*>? {
        val node = SendBuffered(element)
        queue.addLastIfPrev(node, { prev ->
            if (prev is ReceiveOrClosed<*>) return@sendConflated prev
            true
        })
        conflatePreviousSendBuffered(node)
        return null
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun conflatePreviousSendBuffered(node: LockFreeLinkedListNode) {
        val prev = node.prevNode
        (prev as? SendBuffered<*>)?.remove()
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun describeSendBuffered(element: E): AddLastDesc<*> = SendBufferedDesc(queue, element)

    private open class SendBufferedDesc<E>(
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

    private class SendConflatedDesc<E>(
        queue: LockFreeLinkedListHead,
        element: E
    ) : SendBufferedDesc<E>(queue, element) {
        override fun finishOnSuccess(affected: LockFreeLinkedListNode, next: LockFreeLinkedListNode) {
            super.finishOnSuccess(affected, next)
            // remove previous SendBuffered
            (affected as? SendBuffered<*>)?.remove()
        }
    }

    // ------ SendChannel ------

    public final override val isClosedForSend: Boolean get() = closedForSend != null
    public final override val isFull: Boolean get() = queue.nextNode !is ReceiveOrClosed<*> && isBufferFull

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
            // We should check for closed token on offer as well, otherwise offer won't be linearizable
            // in the face of concurrent close()
            result === OFFER_FAILED ->  throw closedForSend?.sendException ?: return false
            result is Closed<*> -> throw result.sendException
            else -> error("offerInternal returned $result")
        }
    }

    private suspend fun sendSuspend(element: E): Unit = suspendAtomicCancellableCoroutine(holdCancellability = true) sc@ { cont ->
        val send = SendElement(element, cont)
        loop@ while (true) {
            val enqueueResult = enqueueSend(send)
            when (enqueueResult) {
                null -> { // enqueued successfully
                    cont.initCancellability() // make it properly cancellable
                    cont.removeOnCancellation(send)
                    return@sc
                }
                is Closed<*> -> {
                    helpClose(enqueueResult)
                    cont.resumeWithException(enqueueResult.sendException)
                    return@sc
                }
            }
            // hm... receiver is waiting or buffer is not full. try to offer
            val offerResult = offerInternal(element)
            when {
                offerResult === OFFER_SUCCESS -> {
                    cont.resume(Unit)
                    return@sc
                }
                offerResult === OFFER_FAILED -> continue@loop
                offerResult is Closed<*> -> {
                    helpClose(offerResult)
                    cont.resumeWithException(offerResult.sendException)
                    return@sc
                }
                else -> error("offerInternal returned $offerResult")
            }
        }
    }

    /**
     * Result is:
     * * null -- successfully enqueued
     * * ENQUEUE_FAILED -- buffer is not full (should not enqueue)
     * * ReceiveOrClosed<*> -- receiver is waiting or it is closed (should not enqueue)
     */
    private fun enqueueSend(send: SendElement): Any? {
        if (isBufferAlwaysFull) {
            queue.addLastIfPrev(send, { prev ->
                if (prev is ReceiveOrClosed<*>) return@enqueueSend prev
                true
            })
        } else {
            if (!queue.addLastIfPrevAndIf(send, { prev ->
                if (prev is ReceiveOrClosed<*>) return@enqueueSend prev
                true
            }, { isBufferFull }))
                return ENQUEUE_FAILED
        }
        return null
    }

    public override fun close(cause: Throwable?): Boolean {
        val closed = Closed<E>(cause)

        /*
         * Try to commit close by adding a close token to the end of the queue.
         * Successful -> we're now responsible for closing receivers
         * Not successful -> help closing pending receivers to maintain invariant
         * "if (!close()) next send will throw"
         */
        val closeAdded = queue.addLastIfPrev(closed, { it !is Closed<*> })
        if (!closeAdded) {
            helpClose(queue.prevNode as Closed<*>)
            return false
        }

        helpClose(closed)
        invokeOnCloseHandler(cause)
        // TODO We can get rid of afterClose
        onClosed(closed)
        afterClose(cause)
        return true
    }

    private fun invokeOnCloseHandler(cause: Throwable?) {
        val handler = onCloseHandler.value
        if (handler !== null && handler !== HANDLER_INVOKED
            && onCloseHandler.compareAndSet(handler, HANDLER_INVOKED)) {
            // CAS failed -> concurrent invokeOnClose() invoked handler
            @Suppress("UNCHECKED_CAST")
            (handler as Handler)(cause)
        }
    }

    override fun invokeOnClose(handler: Handler) {
        // Intricate dance for concurrent invokeOnClose and close calls
        if (!onCloseHandler.compareAndSet(null, handler)) {
            val value = onCloseHandler.value
            if (value === HANDLER_INVOKED) {
                throw IllegalStateException("Another handler was already registered and successfully invoked")
            }

            throw IllegalStateException("Another handler was already registered: $value")
        } else {
            val closedToken = closedForSend
            if (closedToken != null && onCloseHandler.compareAndSet(handler, HANDLER_INVOKED)) {
                // CAS failed -> close() call invoked handler
                (handler)(closedToken.closeCause)
            }
        }
    }

    private fun helpClose(closed: Closed<*>) {
        /*
         * It's important to traverse list from right to left to avoid races with sender.
         * Consider channel state
         * head sentinel -> [receiver 1] -> [receiver 2] -> head sentinel
         * T1 invokes receive()
         * T2 invokes close()
         * T3 invokes close() + send(value)
         *
         * If both will traverse list from left to right, following non-linearizable history is possible:
         * [close -> false], [send -> transferred 'value' to receiver]
         */
        while (true) {
            val previous = closed.prevNode
            // Channel is empty or has no receivers
            if (previous is LockFreeLinkedListHead || previous !is Receive<*>) {
                break
            }

            if (!previous.remove()) {
                // failed to remove the node (due to race) -- retry finding non-removed prevNode
                // NOTE: remove() DOES NOT help pending remove operation (that marked next pointer)
                previous.helpRemove() // make sure remove is complete before continuing
                continue
            }

            @Suppress("UNCHECKED_CAST")
            previous as Receive<E> // type assertion
            previous.resumeReceiveClosed(closed)
        }
    }

    /**
     * Invoked when [Closed] element was just added.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun onClosed(closed: Closed<E>) {}

    /**
     * Invoked after successful [close].
     */
    protected open fun afterClose(cause: Throwable?) {}

    /**
     * Retrieves first receiving waiter from the queue or returns closed token.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun takeFirstReceiveOrPeekClosed(): ReceiveOrClosed<E>? =
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

    private inner class TryEnqueueSendDesc<R>(
        element: E,
        select: SelectInstance<R>,
        block: suspend (SendChannel<E>) -> R
    ) : AddLastDesc<SendSelect<E, R>>(queue, SendSelect(element, this@AbstractSendChannel, select, block)) {
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

    final override val onSend: SelectClause2<E, SendChannel<E>>
        get() = object : SelectClause2<E, SendChannel<E>> {
            override fun <R> registerSelectClause2(select: SelectInstance<R>, param: E, block: suspend (SendChannel<E>) -> R) {
                registerSelectSend(select, param, block)
            }
        }

    private fun <R> registerSelectSend(select: SelectInstance<R>, element: E, block: suspend (SendChannel<E>) -> R) {
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
                        block.startCoroutineUnintercepted(receiver = this, completion = select.completion)
                        return
                    }
                    offerResult is Closed<*> -> throw offerResult.sendException
                    else -> error("offerSelectInternal returned $offerResult")
                }
            }
        }
    }

    // ------ debug ------

    public override fun toString() =
        "$classSimpleName@$hexAddress{$queueDebugStateString}$bufferDebugString"

    private val queueDebugStateString: String
        get() {
            val head = queue.nextNode
            if (head === queue) return "EmptyQueue"
            var result = when (head) {
                is Closed<*> -> head.toString()
                is Receive<*> -> "ReceiveQueued"
                is Send -> "SendQueued"
                else -> "UNEXPECTED:$head" // should not happen
            }
            val tail = queue.prevNode
            if (tail !== head) {
                result += ",queueSize=${countQueueSize()}"
                if (tail is Closed<*>) result += ",closedForSend=$tail"
            }
            return result
        }

    private fun countQueueSize(): Int {
        var size = 0
        queue.forEach<LockFreeLinkedListNode> { size++ }
        return size
    }

    protected open val bufferDebugString: String get() = ""

    // ------ private ------

    private class SendSelect<E, R>(
        override val pollResult: Any?,
        @JvmField val channel: SendChannel<E>,
        @JvmField val select: SelectInstance<R>,
        @JvmField val block: suspend (SendChannel<E>) -> R
    ) : LockFreeLinkedListNode(), Send, DisposableHandle {
        override fun tryResumeSend(idempotent: Any?): Any? =
            if (select.trySelect(idempotent)) SELECT_STARTED else null

        override fun completeResumeSend(token: Any) {
            check(token === SELECT_STARTED)
            block.startCoroutine(receiver = channel, completion = select.completion)
        }

        fun disposeOnSelect() {
            select.disposeOnSelect(this)
        }

        override fun dispose() {
            remove()
        }

        override fun resumeSendClosed(closed: Closed<*>) {
            if (select.trySelect(null))
                select.resumeSelectCancellableWithException(closed.sendException)
        }

        override fun toString(): String = "SendSelect($pollResult)[$channel, $select]"
    }

    private class SendBuffered<out E>(
        @JvmField val element: E
    ) : LockFreeLinkedListNode(), Send {
        override val pollResult: Any? get() = element
        override fun tryResumeSend(idempotent: Any?): Any? = SEND_RESUMED
        override fun completeResumeSend(token: Any) { check(token === SEND_RESUMED) }
        override fun resumeSendClosed(closed: Closed<*>) {}
    }
}

/**
 * Abstract send/receive channel. It is a base class for all channel implementations.
 */
internal abstract class AbstractChannel<E> : AbstractSendChannel<E>(), Channel<E> {
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

    // ------ internal functions for override by buffered channels ------

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
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected val hasReceiveOrClosed: Boolean get() = queue.nextNode is ReceiveOrClosed<*>

    // ------ ReceiveChannel ------

    public final override val isClosedForReceive: Boolean get() = closedForReceive != null && isBufferEmpty
    public final override val isEmpty: Boolean get() = queue.nextNode !is Send && isBufferEmpty

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
    private suspend fun receiveSuspend(): E = suspendAtomicCancellableCoroutine(holdCancellability = true) sc@ { cont ->
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
        if (result) onReceiveEnqueued()
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
    private suspend fun receiveOrNullSuspend(): E? = suspendAtomicCancellableCoroutine(holdCancellability = true) sc@ { cont ->
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

    override fun cancel() {
        @Suppress("DEPRECATION")
        cancel(null)
    }

    override fun cancel(cause: Throwable?): Boolean =
        close(cause).also {
            cleanupSendQueueOnCancel()
        }

    // Note: this function is invoked when channel is already closed
    protected open fun cleanupSendQueueOnCancel() {
        val closed = closedForSend ?: error("Cannot happen")
        while (true) {
            val send = takeFirstSendOrPeekClosed() ?: error("Cannot happen")
            if (send is Closed<*>) {
                check(send === closed)
                return // cleaned
            }
            send.resumeSendClosed(closed)
        }
    }

    public final override fun iterator(): ChannelIterator<E> = Itr(this)

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
            val token = node.tryResumeSend(idempotent = this) ?: return false
            resumeToken = token
            pollResult = node.pollResult as E
            return true
        }
    }

    private inner class TryEnqueueReceiveDesc<E, R>(
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
            onReceiveEnqueued()
            // we can actually remove on select start, but this is also Ok (it'll get removed if discovered there)
            node.removeOnSelectCompletion()
        }
    }

    final override val onReceive: SelectClause1<E>
        get() = object : SelectClause1<E> {
            override fun <R> registerSelectClause1(select: SelectInstance<R>, block: suspend (E) -> R) {
                registerSelectReceive(select, block)
            }
        }

    @Suppress("UNCHECKED_CAST")
    private fun <R> registerSelectReceive(select: SelectInstance<R>, block: suspend (E) -> R) {
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
                        block.startCoroutineUnintercepted(pollResult as E, select.completion)
                        return
                    }
                }
            }
        }
    }

    final override val onReceiveOrNull: SelectClause1<E?>
        get() = object : SelectClause1<E?> {
            override fun <R> registerSelectClause1(select: SelectInstance<R>, block: suspend (E?) -> R) {
                registerSelectReceiveOrNull(select, block)
            }
        }

    @Suppress("UNCHECKED_CAST")
    private fun <R> registerSelectReceiveOrNull(select: SelectInstance<R>, block: suspend (E?) -> R) {
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
                            if (select.trySelect(null))
                                block.startCoroutineUnintercepted(null, select.completion)
                            return
                        } else
                            throw pollResult.closeCause
                    }
                    else -> {
                        // selected successfully
                        block.startCoroutineUnintercepted(pollResult as E, select.completion)
                        return
                    }
                }
            }
        }
    }

    // ------ protected ------

    override fun takeFirstReceiveOrPeekClosed(): ReceiveOrClosed<E>? =
        super.takeFirstReceiveOrPeekClosed().also {
            if (it != null && it !is Closed<*>) onReceiveDequeued()
        }

    /**
     * Invoked when receiver is successfully enqueued to the queue of waiting receivers.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun onReceiveEnqueued() {}

    /**
     * Invoked when enqueued receiver was successfully removed from the queue of waiting receivers.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun onReceiveDequeued() {}

    // ------ private ------

    private fun removeReceiveOnCancel(cont: CancellableContinuation<*>, receive: Receive<*>) =
        cont.invokeOnCancellation(handler = RemoveReceiveOnCancel(receive).asHandler)

    private inner class RemoveReceiveOnCancel(private val receive: Receive<*>) : CancelHandler() {
        override fun invoke(cause: Throwable?) {
            if (receive.remove())
                onReceiveDequeued()
        }
        override fun toString(): String = "RemoveReceiveOnCancel[$receive]"
    }

    private class Itr<E>(val channel: AbstractChannel<E>) : ChannelIterator<E> {
        var result: Any? = POLL_FAILED // E | POLL_FAILED | Closed

        override suspend fun hasNext(): Boolean {
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

        private suspend fun hasNextSuspend(): Boolean = suspendAtomicCancellableCoroutine(holdCancellability = true) sc@ { cont ->
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
        override suspend fun next(): E {
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

    private class ReceiveHasNext<E>(
        @JvmField val iterator: Itr<E>,
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
            if (select.trySelect(null)) {
                if (closed.closeCause == null && nullOnClose) {
                    block.startCoroutine(null, select.completion)
                } else {
                    // even though we are dispatching coroutine to process channel close on receive,
                    // which is an atomically cancellable suspending function,
                    // close is a final state, so we can use a cancellable resume mode
                    select.resumeSelectCancellableWithException(closed.receiveException)
                }
            }
        }

        fun removeOnSelectCompletion() {
            select.disposeOnSelect(this)
        }

        override fun dispose() { // invoked on select completion
            if (remove())
                onReceiveDequeued() // notify cancellation of receive
        }

        override fun toString(): String = "ReceiveSelect[$select,nullOnClose=$nullOnClose]"
    }

    private class IdempotentTokenValue<out E>(
        @JvmField val token: Any,
        @JvmField val value: E
    )
}

@JvmField
@SharedImmutable
internal val OFFER_SUCCESS: Any = Symbol("OFFER_SUCCESS")

@JvmField
@SharedImmutable
internal val OFFER_FAILED: Any = Symbol("OFFER_FAILED")

@JvmField
@SharedImmutable
internal val POLL_FAILED: Any = Symbol("POLL_FAILED")

@JvmField
@SharedImmutable
internal val ENQUEUE_FAILED: Any = Symbol("ENQUEUE_FAILED")

@JvmField
@SharedImmutable
internal val SELECT_STARTED: Any = Symbol("SELECT_STARTED")

@JvmField
@SharedImmutable
internal val NULL_VALUE: Any = Symbol("NULL_VALUE")

@JvmField
@SharedImmutable
internal val CLOSE_RESUMED: Any = Symbol("CLOSE_RESUMED")

@JvmField
@SharedImmutable
internal val SEND_RESUMED: Any = Symbol("SEND_RESUMED")

@JvmField
@SharedImmutable
internal val HANDLER_INVOKED: Any = Symbol("ON_CLOSE_HANDLER_INVOKED")

internal typealias Handler = (Throwable?) -> Unit

/**
 * Represents sending waiter in the queue.
 */
internal interface Send {
    val pollResult: Any? // E | Closed
    fun tryResumeSend(idempotent: Any?): Any?
    fun completeResumeSend(token: Any)
    fun resumeSendClosed(closed: Closed<*>)
}

/**
 * Represents receiver waiter in the queue or closed token.
 */
internal interface ReceiveOrClosed<in E> {
    val offerResult: Any // OFFER_SUCCESS | Closed
    fun tryResumeReceive(value: E, idempotent: Any?): Any?
    fun completeResumeReceive(token: Any)
}

/**
 * Represents sender for a specific element.
 */
@Suppress("UNCHECKED_CAST")
internal class SendElement(
    override val pollResult: Any?,
    @JvmField val cont: CancellableContinuation<Unit>
) : LockFreeLinkedListNode(), Send {
    override fun tryResumeSend(idempotent: Any?): Any? = cont.tryResume(Unit, idempotent)
    override fun completeResumeSend(token: Any) = cont.completeResume(token)
    override fun resumeSendClosed(closed: Closed<*>) = cont.resumeWithException(closed.sendException)
    override fun toString(): String = "SendElement($pollResult)[$cont]"
}

/**
 * Represents closed channel.
 */
internal class Closed<in E>(
    @JvmField val closeCause: Throwable?
) : LockFreeLinkedListNode(), Send, ReceiveOrClosed<E> {
    val sendException: Throwable get() = closeCause ?: ClosedSendChannelException(DEFAULT_CLOSE_MESSAGE)
    val receiveException: Throwable get() = closeCause ?: ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)

    override val offerResult get() = this
    override val pollResult get() = this
    override fun tryResumeSend(idempotent: Any?): Any? = CLOSE_RESUMED
    override fun completeResumeSend(token: Any) { check(token === CLOSE_RESUMED) }
    override fun tryResumeReceive(value: E, idempotent: Any?): Any? = CLOSE_RESUMED
    override fun completeResumeReceive(token: Any) { check(token === CLOSE_RESUMED) }
    override fun resumeSendClosed(closed: Closed<*>) = error("Should be never invoked")
    override fun toString(): String = "Closed[$closeCause]"
}

private abstract class Receive<in E> : LockFreeLinkedListNode(), ReceiveOrClosed<E> {
    override val offerResult get() = OFFER_SUCCESS
    abstract fun resumeReceiveClosed(closed: Closed<*>)
}
