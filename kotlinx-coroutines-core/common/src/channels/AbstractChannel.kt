/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
            val token = receive.tryResumeReceive(element, null)
            if (token != null) {
                assert { token === RESUME_TOKEN }
                receive.completeResumeReceive(element)
                return receive.offerResult
            }
        }
    }

    /**
     * Tries to add element to buffer or to queued receiver if select statement clause was not selected yet.
     * Return type is `ALREADY_SELECTED | OFFER_SUCCESS | OFFER_FAILED | RETRY_ATOMIC | Closed`.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun offerSelectInternal(element: E, select: SelectInstance<*>): Any {
        // offer atomically with select
        val offerOp = describeTryOffer(element)
        val failure = select.performAtomicTrySelect(offerOp)
        if (failure != null) return failure
        val receive = offerOp.result
        receive.completeResumeReceive(element)
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
        queue.addLastIfPrev(SendBuffered(element)) { prev ->
            if (prev is ReceiveOrClosed<*>) return@sendBuffered prev
            true
        }
        return null
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected fun describeSendBuffered(element: E): AddLastDesc<*> = SendBufferedDesc(queue, element)

    private open class SendBufferedDesc<E>(
        queue: LockFreeLinkedListHead,
        element: E
    ) : AddLastDesc<SendBuffered<E>>(queue, SendBuffered(element)) {
        override fun failure(affected: LockFreeLinkedListNode): Any? = when (affected) {
            is Closed<*> -> affected
            is ReceiveOrClosed<*> -> OFFER_FAILED
            else -> null
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
    public final override val isFull: Boolean get() = full
    private val full: Boolean get() = queue.nextNode !is ReceiveOrClosed<*> && isBufferFull // TODO rename to `isFull`

    public final override suspend fun send(element: E) {
        // fast path -- try offer non-blocking
        if (offerInternal(element) === OFFER_SUCCESS) return
        // slow-path does suspend or throws exception
        return sendSuspend(element)
    }

    internal suspend fun sendFair(element: E) {
        if (offerInternal(element) === OFFER_SUCCESS) {
            yield() // Works only on fast path to properly work in sequential use-cases
            return
        }
        return sendSuspend(element)
    }

    public final override fun offer(element: E): Boolean {
        val result = offerInternal(element)
        return when {
            result === OFFER_SUCCESS -> true
            result === OFFER_FAILED -> {
                // We should check for closed token on offer as well, otherwise offer won't be linearizable
                // in the face of concurrent close()
                // See https://github.com/Kotlin/kotlinx.coroutines/issues/359
                throw recoverStackTrace(helpCloseAndGetSendException(closedForSend ?: return false))
            }
            result is Closed<*> -> throw recoverStackTrace(helpCloseAndGetSendException(result))
            else -> error("offerInternal returned $result")
        }
    }

    private fun helpCloseAndGetSendException(closed: Closed<*>): Throwable {
        // To ensure linearizablity we must ALWAYS help close the channel when we observe that it was closed
        // See https://github.com/Kotlin/kotlinx.coroutines/issues/1419
        helpClose(closed)
        return closed.sendException
    }

    private suspend fun sendSuspend(element: E): Unit = suspendAtomicCancellableCoroutineReusable sc@ { cont ->
        loop@ while (true) {
            if (full) {
                val send = SendElement(element, cont)
                val enqueueResult = enqueueSend(send)
                when {
                    enqueueResult == null -> { // enqueued successfully
                        cont.removeOnCancellation(send)
                        return@sc
                    }
                    enqueueResult is Closed<*> -> {
                        cont.helpCloseAndResumeWithSendException(enqueueResult)
                        return@sc
                    }
                    enqueueResult === ENQUEUE_FAILED -> {} // try to offer instead
                    enqueueResult is Receive<*> -> {} // try to offer instead
                    else -> error("enqueueSend returned $enqueueResult")
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
                    cont.helpCloseAndResumeWithSendException(offerResult)
                    return@sc
                }
                else -> error("offerInternal returned $offerResult")
            }
        }
    }

    private fun Continuation<*>.helpCloseAndResumeWithSendException(closed: Closed<*>) {
        helpClose(closed)
        resumeWithException(closed.sendException)
    }

    /**
     * Result is:
     * * null -- successfully enqueued
     * * ENQUEUE_FAILED -- buffer is not full (should not enqueue)
     * * ReceiveOrClosed<*> -- receiver is waiting or it is closed (should not enqueue)
     */
    private fun enqueueSend(send: Send): Any? {
        if (isBufferAlwaysFull) {
            queue.addLastIfPrev(send) { prev ->
                if (prev is ReceiveOrClosed<*>) return@enqueueSend prev
                true
            }
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
        val closeAdded = queue.addLastIfPrev(closed) { it !is Closed<*> }
        val actuallyClosed = if (closeAdded) closed else queue.prevNode as Closed<*>
        helpClose(actuallyClosed)
        if (closeAdded) invokeOnCloseHandler(cause)
        return closeAdded // true if we have closed
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
         * Consider channel state: head -> [receive_1] -> [receive_2] -> head
         * - T1 calls receive()
         * - T2 calls close()
         * - T3 calls close() + send(value)
         *
         * If both will traverse list from left to right, following non-linearizable history is possible:
         * [close -> false], [send -> transferred 'value' to receiver]
         *
         * Another problem with linearizability of close is that we cannot resume closed receives until all
         * receivers are removed from the list.
         * Consider channel state: head -> [receive_1] -> [receive_2] -> head
         * - T1 called receive_2, and will call send() when it's receive call resumes
         * - T2 calls close()
         *
         * Now if T2's close resumes T1's receive_2 then it's receive gets "closed for receive" exception, but
         * its subsequent attempt to send successfully rendezvous with receive_1, producing non-linearizable execution.
         */
        var closedList = InlineList<Receive<E>>()
        while (true) {
            // Break when channel is empty or has no receivers
            @Suppress("UNCHECKED_CAST")
            val previous = closed.prevNode as? Receive<E> ?: break
            if (!previous.remove()) {
                // failed to remove the node (due to race) -- retry finding non-removed prevNode
                // NOTE: remove() DOES NOT help pending remove operation (that marked next pointer)
                previous.helpRemove() // make sure remove is complete before continuing
                continue
            }
            // add removed nodes to a separate list
            closedList += previous
        }
        /*
         * Now notify all removed nodes that the channel was closed
         * in the order they were added to the channel
         */
        closedList.forEachReversed { it.resumeReceiveClosed(closed) }
        // and do other post-processing
        onClosedIdempotent(closed)
    }

    /**
     * Invoked when channel is closed as the last action of [close] invocation.
     * This method should be idempotent and can be called multiple times.
     */
    protected open fun onClosedIdempotent(closed: LockFreeLinkedListNode) {}

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
        override fun failure(affected: LockFreeLinkedListNode): Any? = when (affected) {
            is Closed<*> -> affected
            !is ReceiveOrClosed<*> -> OFFER_FAILED
            else -> null
        }

        @Suppress("UNCHECKED_CAST")
        override fun onPrepare(prepareOp: PrepareOp): Any? {
            val affected = prepareOp.affected as ReceiveOrClosed<E> // see "failure" impl
            val token = affected.tryResumeReceive(element, prepareOp) ?: return REMOVE_PREPARED
            if (token === RETRY_ATOMIC) return RETRY_ATOMIC
            assert { token === RESUME_TOKEN }
            return null
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
            if (full) {
                val node = SendSelect(element, this, select, block)
                val enqueueResult = enqueueSend(node)
                when {
                    enqueueResult == null -> { // enqueued successfully
                        select.disposeOnSelect(node)
                        return
                    }
                    enqueueResult is Closed<*> -> throw recoverStackTrace(helpCloseAndGetSendException(enqueueResult))
                    enqueueResult === ENQUEUE_FAILED -> {} // try to offer
                    enqueueResult is Receive<*> -> {} // try to offer
                    else -> error("enqueueSend returned $enqueueResult ")
                }
            }
            // hm... receiver is waiting or buffer is not full. try to offer
            val offerResult = offerSelectInternal(element, select)
            when {
                offerResult === ALREADY_SELECTED -> return
                offerResult === OFFER_FAILED -> {} // retry
                offerResult === RETRY_ATOMIC -> {} // retry
                offerResult === OFFER_SUCCESS -> {
                    block.startCoroutineUnintercepted(receiver = this, completion = select.completion)
                    return
                }
                offerResult is Closed<*> -> throw recoverStackTrace(helpCloseAndGetSendException(offerResult))
                else -> error("offerSelectInternal returned $offerResult")
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
        @JvmField val channel: AbstractSendChannel<E>,
        @JvmField val select: SelectInstance<R>,
        @JvmField val block: suspend (SendChannel<E>) -> R
    ) : Send(), DisposableHandle {
        override fun tryResumeSend(otherOp: PrepareOp?): Symbol? =
            select.trySelectOther(otherOp) as Symbol? // must return symbol

        override fun completeResumeSend() {
            block.startCoroutine(receiver = channel, completion = select.completion)
        }

        override fun dispose() { // invoked on select completion
            remove()
        }

        override fun resumeSendClosed(closed: Closed<*>) {
            if (select.trySelect())
                select.resumeSelectCancellableWithException(closed.sendException)
        }

        override fun toString(): String = "SendSelect@$hexAddress($pollResult)[$channel, $select]"
    }

    internal class SendBuffered<out E>(
        @JvmField val element: E
    ) : Send() {
        override val pollResult: Any? get() = element
        override fun tryResumeSend(otherOp: PrepareOp?): Symbol? = RESUME_TOKEN.also { otherOp?.finishPrepare() }
        override fun completeResumeSend() {}
        override fun resumeSendClosed(closed: Closed<*>) {}
        override fun toString(): String = "SendBuffered@$hexAddress($element)"
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
            val token = send.tryResumeSend(null)
            if (token != null) {
                assert { token === RESUME_TOKEN }
                send.completeResumeSend()
                return send.pollResult
            }
        }
    }

    /**
     * Tries to remove element from buffer or from queued sender if select statement clause was not selected yet.
     * Return type is `ALREADY_SELECTED | E | POLL_FAILED | RETRY_ATOMIC | Closed`
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun pollSelectInternal(select: SelectInstance<*>): Any? {
        // poll atomically with select
        val pollOp = describeTryPoll()
        val failure = select.performAtomicTrySelect(pollOp)
        if (failure != null) return failure
        val send = pollOp.result
        send.completeResumeSend()
        return pollOp.result.pollResult
    }

    // ------ state functions & helpers for concrete implementations ------

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected val hasReceiveOrClosed: Boolean get() = queue.nextNode is ReceiveOrClosed<*>

    // ------ ReceiveChannel ------

    public final override val isClosedForReceive: Boolean get() = closedForReceive != null && isBufferEmpty
    public final override val isEmpty: Boolean get() = queue.nextNode !is Send && isBufferEmpty

    public final override suspend fun receive(): E {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        /*
         * If result is Closed -- go to tail-call slow-path that will allow us to
         * properly recover stacktrace without paying a performance cost on fast path.
         */
        if (result !== POLL_FAILED && result !is Closed<*>) return receiveResult(result)
        // slow-path does suspend
        return receiveSuspend(RECEIVE_THROWS_ON_CLOSE)
    }

    @Suppress("UNCHECKED_CAST")
    private fun receiveResult(result: Any?): E {
        if (result is Closed<*>) throw recoverStackTrace(result.receiveException)
        return result as E
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun <R> receiveSuspend(receiveMode: Int): R = suspendAtomicCancellableCoroutineReusable sc@ { cont ->
        val receive = ReceiveElement<E>(cont as CancellableContinuation<Any?>, receiveMode)
        while (true) {
            if (enqueueReceive(receive)) {
                removeReceiveOnCancel(cont, receive)
                return@sc
            }
            // hm... something is not right. try to poll
            val result = pollInternal()
            if (result is Closed<*>) {
                receive.resumeReceiveClosed(result)
                return@sc
            }
            if (result !== POLL_FAILED) {
                cont.resume(receive.resumeValue(result as E))
                return@sc
            }
        }
    }

    private fun enqueueReceive(receive: Receive<E>): Boolean {
        val result = if (isBufferAlwaysEmpty)
            queue.addLastIfPrev(receive) { it !is Send } else
            queue.addLastIfPrevAndIf(receive, { it !is Send }, { isBufferEmpty })
        if (result) onReceiveEnqueued()
        return result
    }

    public final override suspend fun receiveOrNull(): E? {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        if (result !== POLL_FAILED) return receiveOrNullResult(result)
        // slow-path does suspend
        return receiveSuspend(RECEIVE_NULL_ON_CLOSE)
    }

    @Suppress("UNCHECKED_CAST")
    private fun receiveOrNullResult(result: Any?): E? {
        if (result is Closed<*>) {
            if (result.closeCause != null) throw recoverStackTrace(result.closeCause)
            return null
        }
        return result as E
    }

    @Suppress("UNCHECKED_CAST")
    public final override suspend fun receiveOrClosed(): ValueOrClosed<E> {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        if (result !== POLL_FAILED) return result.toResult()
        // slow-path does suspend
        return receiveSuspend(RECEIVE_RESULT)
    }

    @Suppress("UNCHECKED_CAST")
    public final override fun poll(): E? {
        val result = pollInternal()
        return if (result === POLL_FAILED) null else receiveOrNullResult(result)
    }

    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    final override fun cancel(cause: Throwable?): Boolean =
        cancelInternal(cause)

    final override fun cancel(cause: CancellationException?) {
        cancelInternal(cause ?: CancellationException("$classSimpleName was cancelled"))
    }

    // It needs to be internal to support deprecated cancel(Throwable?) API
    internal fun cancelInternal(cause: Throwable?): Boolean =
        close(cause).also {
            onCancelIdempotent(it)
        }

    /**
     * Method that is invoked right after [close] in [cancel] sequence.
     * [wasClosed] is directly mapped to the value returned by [close].
     */
    protected open fun onCancelIdempotent(wasClosed: Boolean) {
        /*
         * See the comment to helpClose, all these machinery (reversed order of iteration, postponed resume)
         * has the same rationale.
         */
        val closed = closedForSend ?: error("Cannot happen")
        var list = InlineList<Send>()
        while (true) {
            val previous = closed.prevNode
            if (previous is LockFreeLinkedListHead) {
                break
            }
            assert { previous is Send }
            if (!previous.remove()) {
                previous.helpRemove() // make sure remove is complete before continuing
                continue
            }
            // Add to the list only **after** successful removal
            list += previous as Send
        }
        list.forEachReversed { it.resumeSendClosed(closed) }
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
        override fun failure(affected: LockFreeLinkedListNode): Any? = when (affected) {
            is Closed<*> -> affected
            !is Send -> POLL_FAILED
            else -> null
        }

        @Suppress("UNCHECKED_CAST")
        override fun onPrepare(prepareOp: PrepareOp): Any? {
            val affected = prepareOp.affected as Send // see "failure" impl
            val token = affected.tryResumeSend(prepareOp) ?: return REMOVE_PREPARED
            if (token === RETRY_ATOMIC) return RETRY_ATOMIC
            assert { token === RESUME_TOKEN }
            return null
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
                if (enqueueReceiveSelect(select, block as suspend (Any?) -> R, RECEIVE_THROWS_ON_CLOSE)) return
            } else {
                val pollResult = pollSelectInternal(select)
                when {
                    pollResult === ALREADY_SELECTED -> return
                    pollResult === POLL_FAILED -> {} // retry
                    pollResult === RETRY_ATOMIC -> {} // retry
                    pollResult is Closed<*> -> throw recoverStackTrace(pollResult.receiveException)
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
                if (enqueueReceiveSelect(select, block as suspend (Any?) -> R, RECEIVE_NULL_ON_CLOSE)) return
            } else {
                val pollResult = pollSelectInternal(select)
                when {
                    pollResult === ALREADY_SELECTED -> return
                    pollResult === POLL_FAILED -> {} // retry
                    pollResult === RETRY_ATOMIC -> {} // retry
                    pollResult is Closed<*> -> {
                        if (pollResult.closeCause == null) {
                            if (select.trySelect())
                                block.startCoroutineUnintercepted(null, select.completion)
                            return
                        } else {
                            throw recoverStackTrace(pollResult.closeCause)
                        }
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

    override val onReceiveOrClosed: SelectClause1<ValueOrClosed<E>>
        get() = object : SelectClause1<ValueOrClosed<E>> {
            override fun <R> registerSelectClause1(select: SelectInstance<R>, block: suspend (ValueOrClosed<E>) -> R) {
                registerSelectReceiveOrClosed(select, block)
            }
        }

    @Suppress("UNCHECKED_CAST")
    private fun <R> registerSelectReceiveOrClosed(select: SelectInstance<R>, block: suspend (ValueOrClosed<E>) -> R) {
        while (true) {
            if (select.isSelected) return
            if (isEmpty) {
                if (enqueueReceiveSelect(select, block as suspend (Any?) -> R, RECEIVE_RESULT)) return
            } else {
                val pollResult = pollSelectInternal(select)
                when {
                    pollResult === ALREADY_SELECTED -> return
                    pollResult === POLL_FAILED -> {} // retry
                    pollResult === RETRY_ATOMIC -> {} // retry
                    pollResult is Closed<*> -> {
                        block.startCoroutineUnintercepted(ValueOrClosed.closed(pollResult.closeCause), select.completion)
                    }
                    else -> {
                        // selected successfully
                        block.startCoroutineUnintercepted(ValueOrClosed.value(pollResult as E), select.completion)
                        return
                    }
                }
            }
        }
    }

    private fun <R> enqueueReceiveSelect(
        select: SelectInstance<R>,
        block: suspend (Any?) -> R,
        receiveMode: Int
    ): Boolean {
        val node = ReceiveSelect(this, select, block, receiveMode)
        val result = enqueueReceive(node)
        if (result) select.disposeOnSelect(node)
        return result
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
                if (result.closeCause != null) throw recoverStackTrace(result.receiveException)
                return false
            }
            return true
        }

        private suspend fun hasNextSuspend(): Boolean = suspendAtomicCancellableCoroutineReusable sc@ { cont ->
            val receive = ReceiveHasNext(this, cont)
            while (true) {
                if (channel.enqueueReceive(receive)) {
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
        override fun next(): E {
            val result = this.result
            if (result is Closed<*>) throw recoverStackTrace(result.receiveException)
            if (result !== POLL_FAILED) {
                this.result = POLL_FAILED
                return result as E
            }

            throw IllegalStateException("'hasNext' should be called prior to 'next' invocation")
        }
    }

    private class ReceiveElement<in E>(
        @JvmField val cont: CancellableContinuation<Any?>,
        @JvmField val receiveMode: Int
    ) : Receive<E>() {
        fun resumeValue(value: E): Any? = when (receiveMode) {
            RECEIVE_RESULT -> ValueOrClosed.value(value)
            else -> value
        }

        @Suppress("IMPLICIT_CAST_TO_ANY")
        override fun tryResumeReceive(value: E, otherOp: PrepareOp?): Symbol? {
            val token = cont.tryResume(resumeValue(value), otherOp?.desc) ?: return null
            assert { token === RESUME_TOKEN } // the only other possible result
            // We can call finishPrepare only after successful tryResume, so that only good affected node is saved
            otherOp?.finishPrepare()
            return RESUME_TOKEN
        }

        override fun completeResumeReceive(value: E) = cont.completeResume(RESUME_TOKEN)

        override fun resumeReceiveClosed(closed: Closed<*>) {
            when {
                receiveMode == RECEIVE_NULL_ON_CLOSE && closed.closeCause == null -> cont.resume(null)
                receiveMode == RECEIVE_RESULT -> cont.resume(closed.toResult<Any>())
                else -> cont.resumeWithException(closed.receiveException)
            }
        }
        override fun toString(): String = "ReceiveElement@$hexAddress[receiveMode=$receiveMode]"
    }

    private class ReceiveHasNext<E>(
        @JvmField val iterator: Itr<E>,
        @JvmField val cont: CancellableContinuation<Boolean>
    ) : Receive<E>() {
        override fun tryResumeReceive(value: E, otherOp: PrepareOp?): Symbol? {
            val token = cont.tryResume(true, otherOp?.desc) ?: return null
            assert { token === RESUME_TOKEN } // the only other possible result
            // We can call finishPrepare only after successful tryResume, so that only good affected node is saved
            otherOp?.finishPrepare()
            return RESUME_TOKEN
        }

        override fun completeResumeReceive(value: E) {
            /*
               When otherOp != null invocation of tryResumeReceive can happen multiple times and much later,
               but completeResumeReceive is called once so we set iterator result here.
             */
            iterator.result = value
            cont.completeResume(RESUME_TOKEN)
        }

        override fun resumeReceiveClosed(closed: Closed<*>) {
            val token = if (closed.closeCause == null) {
                cont.tryResume(false)
            } else {
                cont.tryResumeWithException(recoverStackTrace(closed.receiveException, cont))
            }
            if (token != null) {
                iterator.result = closed
                cont.completeResume(token)
            }
        }
        override fun toString(): String = "ReceiveHasNext@$hexAddress"
    }

    private class ReceiveSelect<R, E>(
        @JvmField val channel: AbstractChannel<E>,
        @JvmField val select: SelectInstance<R>,
        @JvmField val block: suspend (Any?) -> R,
        @JvmField val receiveMode: Int
    ) : Receive<E>(), DisposableHandle {
        override fun tryResumeReceive(value: E, otherOp: PrepareOp?): Symbol? =
            select.trySelectOther(otherOp) as Symbol?

        @Suppress("UNCHECKED_CAST")
        override fun completeResumeReceive(value: E) {
            block.startCoroutine(if (receiveMode == RECEIVE_RESULT) ValueOrClosed.value(value) else value, select.completion)
        }

        override fun resumeReceiveClosed(closed: Closed<*>) {
            if (!select.trySelect()) return
            when (receiveMode) {
                RECEIVE_THROWS_ON_CLOSE -> select.resumeSelectCancellableWithException(closed.receiveException)
                RECEIVE_RESULT -> block.startCoroutine(ValueOrClosed.closed<R>(closed.closeCause), select.completion)
                RECEIVE_NULL_ON_CLOSE -> if (closed.closeCause == null) {
                    block.startCoroutine(null, select.completion)
                } else {
                    select.resumeSelectCancellableWithException(closed.receiveException)
                }
            }
        }

        override fun dispose() { // invoked on select completion
            if (remove())
                channel.onReceiveDequeued() // notify cancellation of receive
        }

        override fun toString(): String = "ReceiveSelect@$hexAddress[$select,receiveMode=$receiveMode]"
    }
}

// receiveMode values
internal const val RECEIVE_THROWS_ON_CLOSE = 0
internal const val RECEIVE_NULL_ON_CLOSE = 1
internal const val RECEIVE_RESULT = 2

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
internal val HANDLER_INVOKED: Any = Symbol("ON_CLOSE_HANDLER_INVOKED")

internal typealias Handler = (Throwable?) -> Unit

/**
 * Represents sending waiter in the queue.
 */
internal abstract class Send : LockFreeLinkedListNode() {
    abstract val pollResult: Any? // E | Closed
    // Returns: null - failure,
    //          RETRY_ATOMIC for retry (only when otherOp != null),
    //          RESUME_TOKEN on success (call completeResumeSend)
    // Must call otherOp?.finishPrepare() after deciding on result other than RETRY_ATOMIC
    abstract fun tryResumeSend(otherOp: PrepareOp?): Symbol?
    abstract fun completeResumeSend()
    abstract fun resumeSendClosed(closed: Closed<*>)
}

/**
 * Represents receiver waiter in the queue or closed token.
 */
internal interface ReceiveOrClosed<in E> {
    val offerResult: Any // OFFER_SUCCESS | Closed
    // Returns: null - failure,
    //          RETRY_ATOMIC for retry (only when otherOp != null),
    //          RESUME_TOKEN on success (call completeResumeReceive)
    // Must call otherOp?.finishPrepare() after deciding on result other than RETRY_ATOMIC
    fun tryResumeReceive(value: E, otherOp: PrepareOp?): Symbol?
    fun completeResumeReceive(value: E)
}

/**
 * Represents sender for a specific element.
 */
@Suppress("UNCHECKED_CAST")
internal class SendElement(
    override val pollResult: Any?,
    @JvmField val cont: CancellableContinuation<Unit>
) : Send() {
    override fun tryResumeSend(otherOp: PrepareOp?): Symbol? {
        val token = cont.tryResume(Unit, otherOp?.desc) ?: return null
        assert { token === RESUME_TOKEN } // the only other possible result
        // We can call finishPrepare only after successful tryResume, so that only good affected node is saved
        otherOp?.finishPrepare() // finish preparations
        return RESUME_TOKEN
    }
    override fun completeResumeSend() = cont.completeResume(RESUME_TOKEN)
    override fun resumeSendClosed(closed: Closed<*>) = cont.resumeWithException(closed.sendException)
    override fun toString(): String = "SendElement@$hexAddress($pollResult)"
}

/**
 * Represents closed channel.
 */
internal class Closed<in E>(
    @JvmField val closeCause: Throwable?
) : Send(), ReceiveOrClosed<E> {
    val sendException: Throwable get() = closeCause ?: ClosedSendChannelException(DEFAULT_CLOSE_MESSAGE)
    val receiveException: Throwable get() = closeCause ?: ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)

    override val offerResult get() = this
    override val pollResult get() = this
    override fun tryResumeSend(otherOp: PrepareOp?): Symbol? = RESUME_TOKEN.also { otherOp?.finishPrepare() }
    override fun completeResumeSend() {}
    override fun tryResumeReceive(value: E, otherOp: PrepareOp?): Symbol? = RESUME_TOKEN.also { otherOp?.finishPrepare() }
    override fun completeResumeReceive(value: E) {}
    override fun resumeSendClosed(closed: Closed<*>) = assert { false } // "Should be never invoked"
    override fun toString(): String = "Closed@$hexAddress[$closeCause]"
}

private abstract class Receive<in E> : LockFreeLinkedListNode(), ReceiveOrClosed<E> {
    override val offerResult get() = OFFER_SUCCESS
    abstract fun resumeReceiveClosed(closed: Closed<*>)
}

@Suppress("NOTHING_TO_INLINE", "UNCHECKED_CAST")
private inline fun <E> Any?.toResult(): ValueOrClosed<E> =
    if (this is Closed<*>) ValueOrClosed.closed(closeCause) else ValueOrClosed.value(this as E)

@Suppress("NOTHING_TO_INLINE")
private inline fun <E> Closed<*>.toResult(): ValueOrClosed<E> = ValueOrClosed.closed(closeCause)
