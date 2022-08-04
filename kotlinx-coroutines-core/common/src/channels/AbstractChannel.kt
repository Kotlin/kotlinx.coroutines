/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.selects.TrySelectDetailedResult.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * Abstract send channel. It is a base class for all send channel implementations.
 */
internal abstract class AbstractSendChannel<E>(
    @JvmField protected val onUndeliveredElement: OnUndeliveredElement<E>?
) : SendChannel<E> {
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
     * This operation should be atomic if it is invoked by [enqueueSend].
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
            val token = receive.tryResumeReceive(element)
            if (token != null) {
                assert { token === RESUME_TOKEN }
                receive.completeResumeReceive(element)
                return receive.offerResult
            }
        }
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

    // ------ SendChannel ------

    public final override val isClosedForSend: Boolean get() = closedForSend != null
    private val isFullImpl: Boolean get() = queue.nextNode !is ReceiveOrClosed<*> && isBufferFull

    public final override suspend fun send(element: E) {
        // fast path -- try offer non-blocking
        if (offerInternal(element) === OFFER_SUCCESS) return
        // slow-path does suspend or throws exception
        return sendSuspend(element)
    }

    @Suppress("DEPRECATION", "DEPRECATION_ERROR")
    override fun offer(element: E): Boolean {
        // Temporary migration for offer users who rely on onUndeliveredElement
        try {
            return super.offer(element)
        } catch (e: Throwable) {
            onUndeliveredElement?.callUndeliveredElementCatchingException(element)?.let {
                // If it crashes, add send exception as suppressed for better diagnostics
                it.addSuppressed(e)
                throw it
            }
            throw e
        }
    }

    public final override fun trySend(element: E): ChannelResult<Unit> {
        val result = offerInternal(element)
        return when {
            result === OFFER_SUCCESS -> ChannelResult.success(Unit)
            result === OFFER_FAILED -> {
                // We should check for closed token on trySend as well, otherwise trySend won't be linearizable
                // in the face of concurrent close()
                // See https://github.com/Kotlin/kotlinx.coroutines/issues/359
                val closedForSend = closedForSend ?: return ChannelResult.failure()
                ChannelResult.closed(helpCloseAndGetSendException(closedForSend))
            }
            result is Closed<*> -> {
                ChannelResult.closed(helpCloseAndGetSendException(result))
            }
            else -> error("trySend returned $result")
        }
    }

    private fun helpCloseAndGetSendException(closed: Closed<*>): Throwable {
        helpClose(closed)
        return closed.sendException
    }

    private fun helpCloseAndGetSendException(element: E, closed: Closed<*>): Throwable {
        // To ensure linearizablity we must ALWAYS help close the channel when we observe that it was closed
        // See https://github.com/Kotlin/kotlinx.coroutines/issues/1419
        helpClose(closed)
        // Element was not delivered -> cals onUndeliveredElement
        onUndeliveredElement?.callUndeliveredElementCatchingException(element)?.let {
            // If it crashes, add send exception as suppressed for better diagnostics
            it.addSuppressed(closed.sendException)
            throw it
        }
        return closed.sendException
    }

    private suspend fun sendSuspend(element: E): Unit = suspendCancellableCoroutineReusable sc@ { cont ->
        sendSlowPath(element, cont)
    }

    // waiter is either CancellableContinuation or SelectInstance
    private fun sendSlowPath(element: E, waiter: Any) {
        loop@ while (true) {
            if (isFullImpl) {
                val send: Send = if (waiter is SelectInstance<*>) {
                    if (onUndeliveredElement == null) SendElementSelect(element, waiter, this)
                    else SendElementSelectWithUndeliveredHandler(element, waiter, this, onUndeliveredElement)
                } else {
                    if (onUndeliveredElement == null) SendElement(element, waiter as CancellableContinuation<Unit>)
                    else SendElementWithUndeliveredHandler(element, waiter as CancellableContinuation<Unit>, onUndeliveredElement)
                }
                val enqueueResult = enqueueSend(send)
                when {
                    enqueueResult == null -> { // enqueued successfully
                        if (waiter is SelectInstance<*>) {
                            waiter.disposeOnCompletion { send.remove() }
                        } else {
                            waiter as CancellableContinuation<Unit>
                            waiter.removeOnCancellation(send)
                        }
                        return
                    }
                    enqueueResult is Closed<*> -> {
                        if (waiter is SelectInstance<*>) {
                            waiter.helpCloseAndSelectInRegistrationPhaseClosed(element, enqueueResult)
                        } else {
                            waiter as CancellableContinuation<Unit>
                            waiter.helpCloseAndResumeWithSendException(element, enqueueResult)
                        }
                        return
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
                    if (waiter is SelectInstance<*>) {
                        waiter.selectInRegistrationPhase(Unit)
                    } else {
                        waiter as CancellableContinuation<Unit>
                        waiter.resume(Unit)
                    }
                    return
                }
                offerResult === OFFER_FAILED -> continue@loop
                offerResult is Closed<*> -> {
                    if (waiter is SelectInstance<*>) {
                        waiter.helpCloseAndSelectInRegistrationPhaseClosed(element, offerResult)
                    } else {
                        waiter as CancellableContinuation<Unit>
                        waiter.helpCloseAndResumeWithSendException(element, offerResult)
                    }
                    return
                }
                else -> error("offerInternal returned $offerResult")
            }
        }
    }

    private fun Continuation<*>.helpCloseAndResumeWithSendException(element: E, closed: Closed<*>) {
        helpClose(closed)
        val sendException = closed.sendException
        onUndeliveredElement?.callUndeliveredElementCatchingException(element)?.let {
            it.addSuppressed(sendException)
            resumeWithException(it)
            return
        }
        resumeWithException(sendException)
    }

    private fun SelectInstance<*>.helpCloseAndSelectInRegistrationPhaseClosed(element: E, closed: Closed<*>) {
        helpClose(closed)
        onUndeliveredElement?.callUndeliveredElementCatchingException(element)?.let {
            it.addSuppressed(closed.sendException)
            selectInRegistrationPhase(Closed<E>(it))
            return
        }
        selectInRegistrationPhase(closed)
    }

    /**
     * Result is:
     * * null -- successfully enqueued
     * * ENQUEUE_FAILED -- buffer is not full (should not enqueue)
     * * ReceiveOrClosed<*> -- receiver is waiting or it is closed (should not enqueue)
     */
    protected open fun enqueueSend(send: Send): Any? {
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

    final override val onSend
        get() = SelectClause2Impl<E, SendChannel<E>>(
            clauseObject = this,
            regFunc = AbstractSendChannel<*>::registerSelectForSend as RegistrationFunction,
            processResFunc = AbstractSendChannel<*>::processResultSelectSend as ProcessResultFunction
        )

    private fun registerSelectForSend(select: SelectInstance<*>, element: Any?) {
        element as E
        if (offerInternal(element) === OFFER_SUCCESS) {
            select.selectInRegistrationPhase(Unit)
            return
        }
        sendSlowPath(element, select)
    }

    private fun processResultSelectSend(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult is Closed<*>) throw selectResult.sendException
        else this

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

    internal class SendBuffered<out E>(
        @JvmField val element: E
    ) : Send() {
        override val pollResult: Any? get() = element
        override fun tryResumeSend(otherOp: PrepareOp?): Symbol? = RESUME_TOKEN.also { otherOp?.finishPrepare() }
        override fun completeResumeSend() {}

        /**
         * This method should be never called, see special logic in [LinkedListChannel.onCancelIdempotentList].
         */
        override fun resumeSendClosed(closed: Closed<*>) {
            assert { false }
        }

        override fun toString(): String = "SendBuffered@$hexAddress($element)"
    }
}

/**
 * Abstract send/receive channel. It is a base class for all channel implementations.
 */
internal abstract class AbstractChannel<E>(
    onUndeliveredElement: OnUndeliveredElement<E>?
) : AbstractSendChannel<E>(onUndeliveredElement), Channel<E> {
    // ------ extension points for buffered channels ------

    /**
     * Returns `true` if [isBufferEmpty] is always `true`.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected abstract val isBufferAlwaysEmpty: Boolean

    /**
     * Returns `true` if this channel's buffer is empty.
     * This operation should be atomic if it is invoked by [enqueueReceive].
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
            // Too late, already cancelled, but we removed it from the queue and need to notify on undelivered element.
            // The only exception is when this "send" operation is an `onSend` clause that has to be re-registered
            // in the corresponding `select` invocation.
            if (!(send is SendElementSelectWithUndeliveredHandler<*> && send.trySelectResult == REREGISTER))
                send.undeliveredElement()
        }
    }

    // ------ state functions & helpers for concrete implementations ------

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected val hasReceiveOrClosed: Boolean get() = queue.nextNode is ReceiveOrClosed<*>

    // ------ ReceiveChannel ------

    public override val isClosedForReceive: Boolean get() = closedForReceive != null && isBufferEmpty
    public override val isEmpty: Boolean get() = isEmptyImpl
    protected val isEmptyImpl: Boolean get() = queue.nextNode !is Send && isBufferEmpty

    public final override suspend fun receive(): E {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        /*
         * If result is Closed -- go to tail-call slow-path that will allow us to
         * properly recover stacktrace without paying a performance cost on fast path.
         * We prefer to recover stacktrace using suspending path to have a more precise stacktrace.
         */
        @Suppress("UNCHECKED_CAST")
        if (result !== POLL_FAILED && result !is Closed<*>) return result as E
        // slow-path does suspend
        return receiveSuspend(RECEIVE_THROWS_ON_CLOSE)
    }

    @Suppress("UNCHECKED_CAST")
    private suspend fun <R> receiveSuspend(receiveMode: Int): R = suspendCancellableCoroutineReusable sc@ { cont ->
        receiveSlowPath(receiveMode, cont)
    }

    @Suppress("UNCHECKED_CAST")
    private fun receiveSlowPath(receiveMode: Int, waiter: Any) {
        val receive = if (waiter is SelectInstance<*>) {
            if (onUndeliveredElement == null) ReceiveElementSelect(waiter)
            else ReceiveElementSelectWithUndeliveredHandler(waiter, onUndeliveredElement)
        } else {
            waiter as CancellableContinuation<Any?>
            if (onUndeliveredElement == null) ReceiveElement(waiter, receiveMode)
            else ReceiveElementWithUndeliveredHandler(waiter, receiveMode, onUndeliveredElement)
        }
        while (true) {
            if (enqueueReceive(receive)) {
                if (waiter is SelectInstance<*>) {
                    waiter.disposeOnCompletion(RemoveReceiveOnCancel(receive))
                } else {
                    waiter as CancellableContinuation<Any?>
                    removeReceiveOnCancel(waiter, receive)
                }
                return
            }
            // hm... something is not right. try to poll
            val result = pollInternal()
            if (result is Closed<*>) {
                if (waiter is SelectInstance<*>) {
                    waiter.selectInRegistrationPhase(result)
                } else { // CancellableContinuation
                    receive.resumeReceiveClosed(result)
                }
                return
            }
            if (result !== POLL_FAILED) {
                if (waiter is SelectInstance<*>) {
                    waiter.selectInRegistrationPhase(result as E)
                } else {
                    waiter as CancellableContinuation<Any?>
                    receive as ReceiveElement
                    waiter.resume(receive.resumeValue(result as E), receive.resumeOnCancellationFun(result as E))
                }
                return
            }
        }
    }

    protected open fun enqueueReceiveInternal(receive: Receive<E>): Boolean = if (isBufferAlwaysEmpty)
        queue.addLastIfPrev(receive) { it !is Send } else
        queue.addLastIfPrevAndIf(receive, { it !is Send }, { isBufferEmpty })

    private fun enqueueReceive(receive: Receive<E>) = enqueueReceiveInternal(receive).also { result ->
        if (result) onReceiveEnqueued()
    }

    @Suppress("UNCHECKED_CAST")
    public final override suspend fun receiveCatching(): ChannelResult<E> {
        // fast path -- try poll non-blocking
        val result = pollInternal()
        if (result !== POLL_FAILED) return result.toResult()
        // slow-path does suspend
        return receiveSuspend(RECEIVE_RESULT)
    }

    @Suppress("UNCHECKED_CAST")
    public final override fun tryReceive(): ChannelResult<E> {
        val result = pollInternal()
        if (result === POLL_FAILED) return ChannelResult.failure()
        if (result is Closed<*>) return ChannelResult.closed(result.closeCause)
        return ChannelResult.success(result as E)
    }

    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    final override fun cancel(cause: Throwable?): Boolean =
        cancelInternal(cause)

    final override fun cancel(cause: CancellationException?) {
        /*
         * Do not create an exception if channel is already cancelled.
         * Channel is closed for receive when either it is cancelled (then we are free to bail out)
         * or was closed and elements were received.
         * Then `onCancelIdempotent` does nothing for all implementations.
         */
        if (isClosedForReceive) return
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
        onCancelIdempotentList(list, closed)
    }

    /**
     * This method is overridden by [LinkedListChannel] to handle cancellation of [SendBuffered] elements from the list.
     */
    protected open fun onCancelIdempotentList(list: InlineList<Send>, closed: Closed<*>) {
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

        override fun onRemoved(affected: LockFreeLinkedListNode) {
            // Called when we removed it from the queue but were too late to resume, so we have undelivered element
            (affected as Send).undeliveredElement()
        }
    }

    // ------ the `select` expression support ------

    final override val onReceive
        get() = SelectClause1Impl<E>(
            clauseObject = this,
            regFunc = AbstractChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = AbstractChannel<*>::processResultSelectReceive as ProcessResultFunction,
            onCancellationConstructor = onUndeliveredElementReceiveCancellationConstructor
        )

    final override val onReceiveCatching
        get() = SelectClause1Impl<ChannelResult<E>>(
            clauseObject = this,
            regFunc = AbstractChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = AbstractChannel<*>::processResultSelectReceiveCatching as ProcessResultFunction,
            onCancellationConstructor = onUndeliveredElementReceiveCancellationConstructor
        )

    override val onReceiveOrNull: SelectClause1<E?>
        get() = SelectClause1Impl<E?>(
            clauseObject = this,
            regFunc = AbstractChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = AbstractChannel<*>::processResultSelectReceiveOrNull as ProcessResultFunction,
            onCancellationConstructor = onUndeliveredElementReceiveCancellationConstructor
        )

    private fun registerSelectForReceive(select: SelectInstance<*>, ignoredParam: Any?) {
        val result = pollInternal()
        if (result !== POLL_FAILED && result !is Closed<*>) {
            select.selectInRegistrationPhase(result as E)
            return
        }
        receiveSlowPath(RECEIVE_RESULT, select)
    }

    private fun processResultSelectReceive(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult is Closed<*>) throw selectResult.receiveException
        else selectResult as E

    private fun processResultSelectReceiveCatching(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult is Closed<*>) ChannelResult.closed(selectResult.closeCause)
        else ChannelResult.success(selectResult as E)

    private fun processResultSelectReceiveOrNull(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult is Closed<*>) null
        else selectResult as E

    private val onUndeliveredElementReceiveCancellationConstructor: OnCancellationConstructor? = onUndeliveredElement?.let {
        { select: SelectInstance<*>, ignoredParam: Any?, element: Any? ->
            { cause: Throwable -> if (element !is Closed<*>) onUndeliveredElement.callUndeliveredElement(element as E, select.context) }
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

    private inner class RemoveReceiveOnCancel(private val receive: Receive<*>) : BeforeResumeCancelHandler(), DisposableHandle {
        override fun invoke(cause: Throwable?) = dispose()

        override fun dispose() {
            if (receive.remove())
                onReceiveDequeued()
        }

        override fun toString(): String = "RemoveReceiveOnCancel[$receive]"
    }

    private class Itr<E>(@JvmField val channel: AbstractChannel<E>) : ChannelIterator<E> {
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

        private suspend fun hasNextSuspend(): Boolean = suspendCancellableCoroutineReusable sc@ { cont ->
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
                    @Suppress("UNCHECKED_CAST")
                    cont.resume(true, channel.onUndeliveredElement?.bindCancellationFun(result as E, cont.context))
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

    private open class ReceiveElement<in E>(
        @JvmField val cont: CancellableContinuation<Any?>,
        @JvmField val receiveMode: Int
    ) : Receive<E>() {
        fun resumeValue(value: E): Any? = when (receiveMode) {
            RECEIVE_RESULT -> ChannelResult.success(value)
            else -> value
        }

        override fun tryResumeReceive(value: E): Symbol? {
            val token = cont.tryResume(resumeValue(value), null, resumeOnCancellationFun(value)) ?: return null
            assert { token === RESUME_TOKEN } // the only other possible result
            return RESUME_TOKEN
        }

        override fun completeResumeReceive(value: E) = cont.completeResume(RESUME_TOKEN)

        override fun resumeReceiveClosed(closed: Closed<*>) {
            when (receiveMode) {
                RECEIVE_RESULT -> cont.resume(closed.toResult<Any>())
                else -> cont.resumeWithException(closed.receiveException)
            }
        }
        override fun toString(): String = "ReceiveElement@$hexAddress[receiveMode=$receiveMode]"
    }

    private class ReceiveElementWithUndeliveredHandler<in E>(
        cont: CancellableContinuation<Any?>,
        receiveMode: Int,
        @JvmField val onUndeliveredElement: OnUndeliveredElement<E>
    ) : ReceiveElement<E>(cont, receiveMode) {
        override fun resumeOnCancellationFun(value: E): ((Throwable) -> Unit)? =
            onUndeliveredElement.bindCancellationFun(value, cont.context)
    }

    internal open inner class ReceiveElementSelect<in E>(
        @JvmField val select: SelectInstance<*>,
    ) : Receive<E>() {
        private val lock = ReentrantLock()
        private var success: Boolean? = null

        override fun tryResumeReceive(value: E): Symbol? = lock.withLock {
            if (success == null) success = select.trySelect(this@AbstractChannel, value)
            if (success!!) RESUME_TOKEN else null
        }
        override fun completeResumeReceive(value: E) {}

        override fun resumeReceiveClosed(closed: Closed<*>) {
            select.trySelect(this@AbstractChannel, closed)
        }
        override fun toString(): String = "ReceiveElementSelect@$hexAddress"
    }

    private open inner class ReceiveElementSelectWithUndeliveredHandler<in E>(
        select: SelectInstance<*>,
        @JvmField val onUndeliveredElement: OnUndeliveredElement<E>
    ) : ReceiveElementSelect<E>(select) {
        override fun resumeOnCancellationFun(value: E): ((Throwable) -> Unit)? =
            onUndeliveredElement.bindCancellationFun(value, select.context)
    }

    private open class ReceiveHasNext<E>(
        @JvmField val iterator: Itr<E>,
        @JvmField val cont: CancellableContinuation<Boolean>
    ) : Receive<E>() {
        override fun tryResumeReceive(value: E): Symbol? {
            val token = cont.tryResume(true, null, resumeOnCancellationFun(value))
                ?: return null
            assert { token === RESUME_TOKEN } // the only other possible result
            return RESUME_TOKEN
        }

        override fun completeResumeReceive(value: E) {
            iterator.result = value
            cont.completeResume(RESUME_TOKEN)
        }

        override fun resumeReceiveClosed(closed: Closed<*>) {
            val token = if (closed.closeCause == null) {
                cont.tryResume(false)
            } else {
                cont.tryResumeWithException(closed.receiveException)
            }
            if (token != null) {
                iterator.result = closed
                cont.completeResume(token)
            }
        }

        override fun resumeOnCancellationFun(value: E): ((Throwable) -> Unit)? =
            iterator.channel.onUndeliveredElement?.bindCancellationFun(value, cont.context)

        override fun toString(): String = "ReceiveHasNext@$hexAddress"
    }
}

// receiveMode values
internal const val RECEIVE_THROWS_ON_CLOSE = 0
internal const val RECEIVE_RESULT = 1

@JvmField
internal val EMPTY = Symbol("EMPTY") // marker for Conflated & Buffered channels

@JvmField
internal val OFFER_SUCCESS = Symbol("OFFER_SUCCESS")

@JvmField
internal val OFFER_FAILED = Symbol("OFFER_FAILED")

@JvmField
internal val POLL_FAILED = Symbol("POLL_FAILED")

@JvmField
internal val ENQUEUE_FAILED = Symbol("ENQUEUE_FAILED")

@JvmField
internal val HANDLER_INVOKED = Symbol("ON_CLOSE_HANDLER_INVOKED")

internal typealias Handler = (Throwable?) -> Unit

/**
 * Represents sending waiter in the queue.
 */
internal abstract class
Send : LockFreeLinkedListNode() {
    abstract val pollResult: Any? // E | Closed - the result pollInternal returns when it rendezvous with this node
    // Returns: null - failure,
    //          RETRY_ATOMIC for retry (only when otherOp != null),
    //          RESUME_TOKEN on success (call completeResumeSend)
    // Must call otherOp?.finishPrepare() after deciding on result other than RETRY_ATOMIC
    abstract fun tryResumeSend(otherOp: PrepareOp?): Symbol?
    abstract fun completeResumeSend()
    abstract fun resumeSendClosed(closed: Closed<*>)
    open fun undeliveredElement() {}
}

/**
 * Represents receiver waiter in the queue or closed token.
 */
internal interface ReceiveOrClosed<in E> {
    val offerResult: Any // OFFER_SUCCESS | Closed
    // Returns: null - failure,
    //          RESUME_TOKEN on success (call completeResumeReceive)
    fun tryResumeReceive(value: E): Symbol?
    fun completeResumeReceive(value: E)
}

/**
 * Represents sender for a specific element.
 */
internal open class SendElement<E>(
    override val pollResult: E,
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
    override fun toString(): String = "$classSimpleName@$hexAddress($pollResult)"
}

internal open class SendElementSelect<E>(
    override val pollResult: E,
    @JvmField val select: SelectInstance<*>,
    private val channel: SendChannel<E>
) : Send() {
    private val lock = ReentrantLock()
    private var _trySelectResult: TrySelectDetailedResult? = null

    override fun tryResumeSend(otherOp: PrepareOp?): Symbol? = lock.withLock {
        select as SelectImplementation<*>
        if (_trySelectResult == null) {
            _trySelectResult = select.trySelectDetailed(channel, Unit)
        }
        return@withLock if (_trySelectResult == SUCCESSFUL) {
            otherOp?.finishPrepare() // finish preparations
            RESUME_TOKEN
        } else null
    }

    val trySelectResult: TrySelectDetailedResult
        get() = checkNotNull(_trySelectResult) { "trySelect(..) has not been invoked yet" }

    override fun completeResumeSend() {}
    override fun resumeSendClosed(closed: Closed<*>) {
        select.trySelect(channel, closed)
    }
    override fun toString(): String = "$classSimpleName@$hexAddress($pollResult)"
}

internal class SendElementWithUndeliveredHandler<E>(
    pollResult: E,
    cont: CancellableContinuation<Unit>,
    @JvmField val onUndeliveredElement: OnUndeliveredElement<E>
) : SendElement<E>(pollResult, cont) {
    override fun remove(): Boolean {
        if (!super.remove()) return false
        // if the node was successfully removed (meaning it was added but was not received) then we have undelivered element
        undeliveredElement()
        return true
    }

    override fun undeliveredElement() {
        onUndeliveredElement.callUndeliveredElement(pollResult, cont.context)
    }
}

internal class SendElementSelectWithUndeliveredHandler<E>(
    pollResult: E,
    select: SelectInstance<*>,
    channel: SendChannel<E>,
    onUndeliveredElement: OnUndeliveredElement<E>
) : SendElementSelect<E>(pollResult, select, channel) {
    private val onUndeliveredElement = atomic<OnUndeliveredElement<E>?>(onUndeliveredElement)

    override fun remove(): Boolean {
        undeliveredElement()
        return super.remove()
    }

    override fun undeliveredElement() {
        onUndeliveredElement.getAndSet(null)?.callUndeliveredElement(pollResult, select.context)
    }
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
    override fun tryResumeSend(otherOp: PrepareOp?): Symbol = RESUME_TOKEN.also { otherOp?.finishPrepare() }
    override fun completeResumeSend() {}
    override fun tryResumeReceive(value: E): Symbol = RESUME_TOKEN
    override fun completeResumeReceive(value: E) {}
    override fun resumeSendClosed(closed: Closed<*>) = assert { false } // "Should be never invoked"
    override fun toString(): String = "Closed@$hexAddress[$closeCause]"
}

internal abstract class Receive<in E> : LockFreeLinkedListNode(), ReceiveOrClosed<E> {
    override val offerResult get() = OFFER_SUCCESS
    abstract fun resumeReceiveClosed(closed: Closed<*>)
    open fun resumeOnCancellationFun(value: E): ((Throwable) -> Unit)? = null
}

@Suppress("NOTHING_TO_INLINE", "UNCHECKED_CAST")
private inline fun <E> Any?.toResult(): ChannelResult<E> =
    if (this is Closed<*>) ChannelResult.closed(closeCause) else ChannelResult.success(this as E)

@Suppress("NOTHING_TO_INLINE")
private inline fun <E> Closed<*>.toResult(): ChannelResult<E> = ChannelResult.closed(closeCause)
