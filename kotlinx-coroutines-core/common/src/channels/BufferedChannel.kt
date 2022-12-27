@file:Suppress("PrivatePropertyName")

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.ChannelResult.Companion.closed
import kotlinx.coroutines.channels.ChannelResult.Companion.success
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.selects.TrySelectDetailedResult.*
import kotlinx.coroutines.sync.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.js.*
import kotlin.jvm.*
import kotlin.math.*
import kotlin.random.*
import kotlin.reflect.*

internal class WaitingSend<E>(val element: E, val channel: BufferedChannel<E>, val sender: CancellableContinuation<Unit>)
internal class WaitingReceive<E>(val channel: BufferedChannel<E>, val receiver: CancellableContinuation<E>)

internal open class BufferedChannel<E>(
    /**
     * Channel capacity; `Channel.RENDEZVOUS` for rendezvous channel
     * and `Channel.UNLIMITED` for unlimited capacity.
     */
    private val capacity: Int,
    @JvmField
    internal val onUndeliveredElement: OnUndeliveredElement<E>? = null
) : Channel<E> {
    init {
        require(capacity >= 0) { "Invalid channel capacity: $capacity, should be >=0" }
        // This implementation has second `init`.
    }

    /*
      The counters indicate the total numbers of send, receive, and buffer expansion calls
      ever performed. The counters are incremented in the beginning of the corresponding
      operation; thus, acquiring a unique (for the operation type) cell to process.
      The segments reference to the last working one for each operation type.

      Notably, the counter for send is combined with the channel closing status
      for synchronization simplicity and performance reasons.

      The logical end of the buffer is initialized with the channel capacity.
      If the channel is rendezvous or unlimited, the counter equals `BUFFER_END_RENDEZVOUS`
      or `BUFFER_END_RENDEZVOUS`, respectively, and never updates. The `bufferEndSegment`
      point to a special `NULL_SEGMENT` in this case.
     */
    private val closed = atomic(0)
    private val enqIdx = atomic(0L)
    private val deqIdx = atomic(0L)

    internal val enqPermits = SemaphoreImpl(permits = capacity, acquiredPermits = 0)
    internal val deqPermits = SemaphoreImpl(permits = Int.MAX_VALUE / 2, acquiredPermits = Int.MAX_VALUE / 2)

    private val isRendezvous get() = capacity == Channel.RENDEZVOUS
    internal val isUnlimited get() = capacity == Channel.UNLIMITED
    private val isRendezvousOrUnlimited get() = isRendezvous || isUnlimited

    private val enqSegment: AtomicRef<ChannelSegment<E>>
    private val deqSegment: AtomicRef<ChannelSegment<E>>

    init {
        @Suppress("LeakingThis")
        val firstSegment = ChannelSegment<E>(id = 0, prev = null, pointers = 2)
        enqSegment = atomic(firstSegment)
        deqSegment = atomic(firstSegment)
    }

    // #########################
    // ## The send operations ##
    // #########################

    override suspend fun send(element: E) {
        if (isUnlimited || enqPermits.acquireFastPath()) {
            enqueue(element)
            deqPermits.release()
        } else {
            sendCompleteSlowPath(element) // tail-call optimization here
        }
    }

    private suspend fun sendCompleteSlowPath(element: E) = suspendCancellableCoroutineReusable { cont ->
        enqPermits.acquireSlowPathSend(WaitingSend(element, this, cont))
    }

    internal fun enqueue(element: E) {
        var segment = enqSegment.value
        while (true) {
            val globalIndex = enqIdx.getAndIncrement()
            val segmentId = globalIndex / SEGMENT_SIZE
            val index = (globalIndex % SEGMENT_SIZE).toInt()
            if (segment.id < segmentId) {
                segment = findSegmentEnq(segmentId, segment)
            }
            if (segment.cas(index, null, element)) return
        }
    }

    override suspend fun receive(): E {
        return if (deqPermits.acquireFastPath()) {
            val element = dequeue()
            if (!isUnlimited) enqPermits.release()
            element
        } else {
            receiveCompleteSlowPath()
        }
    }

    private suspend fun receiveCompleteSlowPath(): E = suspendCancellableCoroutineReusable { cont ->
        deqPermits.acquireSlowPathReceive(WaitingReceive(this, cont))
    }

    internal fun dequeue(): E {
        var segment = deqSegment.value
        while (true) {
            val globalIndex = deqIdx.getAndIncrement()
            val segmentId = globalIndex / SEGMENT_SIZE
            val index = (globalIndex % SEGMENT_SIZE).toInt()
            if (segment.id < segmentId) {
                segment = findSegmentDeq(segmentId, segment)
            }
            var element = segment.get(index)
            if (element == null) {
                element = segment.getAndSet(index, POISONED)
            }
            if (element != null) {
                segment.lazySet(index, DONE)
                @Suppress("UNCHECKED_CAST")
                return element as E
            }
        }
    }

    override fun trySend(element: E): ChannelResult<Unit> = TODO()
    internal open suspend fun sendBroadcast(element: E): Boolean = TODO()
    internal open fun shouldSendSuspend(): Boolean = TODO()

    // ##########################
    // # The receive operations #
    // ##########################

    /**
     * This function is invoked when a receiver is added as a waiter in this channel.
     */
    protected open fun onReceiveEnqueued() {}

    /**
     * This function is invoked when a waiting receiver is no longer stored in this channel;
     * independently on whether it is caused by rendezvous, cancellation, or channel closing.
     */
    protected open fun onReceiveDequeued() {}

    /**
     * This function is invoked when the receiving operation ([receive], [tryReceive],
     * [BufferedChannelIterator.hasNext], etc.) finishes its synchronization -- either
     * completing due to an element retrieving or discovering this channel in the closed state,
     * or deciding to suspend if this channel is empty and not closed.
     *
     * We use this function to protect all receive operations with global lock in [ConflatedBroadcastChannel],
     * by acquiring the lock in the beginning of each operation and releasing it when the synchronization
     * completes, via this function.
     */
    protected open fun onReceiveSynchronizationCompleted() {}

    /*
    The implementation is exactly the same as of `receive()`,
    with the only difference that this function returns a `ChannelResult`
    instance and does not throw exception explicitly in case the channel
    is already closed for receiving. Please refer the plain `receive()`
    implementation for the comments.
    */
    override suspend fun receiveCatching(): ChannelResult<E> = TODO()

    override fun tryReceive(): ChannelResult<E> =
        tryReceiveInternal().also { onReceiveSynchronizationCompleted() }

    /**
     * This internal implementation does not invoke [onReceiveSynchronizationCompleted].
     */
    protected fun tryReceiveInternal(): ChannelResult<E> = TODO()


    // #######################
    // ## Select Expression ##
    // #######################

    @Suppress("UNCHECKED_CAST")
    override val onSend: SelectClause2<E, BufferedChannel<E>>
        get() = SelectClause2Impl(
            clauseObject = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForSend as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectSend as ProcessResultFunction
        )

    @Suppress("UNCHECKED_CAST")
    protected open fun registerSelectForSend(select: SelectInstance<*>, element: Any?): Unit =
        TODO()

    @Suppress("UNUSED_PARAMETER", "RedundantNullableReturnType")
    private fun processResultSelectSend(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CHANNEL_CLOSED) throw sendException
        else this

    @Suppress("UNCHECKED_CAST")
    override val onReceive: SelectClause1<E>
        get() = SelectClause1Impl(
            clauseObject = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectReceive as ProcessResultFunction,
            onCancellationConstructor = onUndeliveredElementReceiveCancellationConstructor
        )

    @Suppress("UNCHECKED_CAST")
    override val onReceiveCatching: SelectClause1<ChannelResult<E>>
        get() = SelectClause1Impl(
            clauseObject = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectReceiveCatching as ProcessResultFunction,
            onCancellationConstructor = onUndeliveredElementReceiveCancellationConstructor
        )

    @Suppress("OVERRIDE_DEPRECATION", "UNCHECKED_CAST")
    override val onReceiveOrNull: SelectClause1<E?>
        get() = SelectClause1Impl(
            clauseObject = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectReceiveOrNull as ProcessResultFunction,
            onCancellationConstructor = onUndeliveredElementReceiveCancellationConstructor
        )

    protected open fun registerSelectForReceive(select: SelectInstance<*>, ignoredParam: Any?): Unit =
        TODO()

    @Suppress("UNUSED_PARAMETER")
    private fun processResultSelectReceive(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CHANNEL_CLOSED) throw receiveException
        else selectResult

    @Suppress("UNUSED_PARAMETER")
    private fun processResultSelectReceiveOrNull(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CHANNEL_CLOSED) {
            if (closeCause == null) null
            else throw receiveException
        } else selectResult

    @Suppress("UNCHECKED_CAST", "UNUSED_PARAMETER", "RedundantNullableReturnType")
    private fun processResultSelectReceiveCatching(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CHANNEL_CLOSED) closed(closeCause)
        else success(selectResult as E)

    @Suppress("UNCHECKED_CAST")
    private val onUndeliveredElementReceiveCancellationConstructor: OnCancellationConstructor? = onUndeliveredElement?.let {
        { select: SelectInstance<*>, _: Any?, element: Any? ->
            { if (element !== CHANNEL_CLOSED) onUndeliveredElement.callUndeliveredElement(element as E, select.context) }
        }
    }

    // ######################
    // ## Iterator Support ##
    // ######################

    override fun iterator(): ChannelIterator<E> = BufferedChannelIterator()

    /**
     * The key idea is that an iterator is a special receiver type,
     * which should be resumed differently to [receive] and [onReceive]
     * operations, but can be served as a waiter in a way similar to
     * [CancellableContinuation] and [SelectInstance].
     *
     * Roughly, [hasNext] is a [receive] sibling, while [next] simply
     * returns the already retrieved element. From the implementation
     * side, [receiveResult] stores the element retrieved by [hasNext]
     * (or a special [CHANNEL_CLOSED] token if the channel is closed).
     *
     * The [invoke] function is a [CancelHandler] implementation,
     * which requires knowing the [segment] and the [index] in it
     * that specify the location of the stored iterator.
     *
     * To resume the suspended [hasNext] call, a special [tryResumeHasNext]
     * function should be used in a way similar to [CancellableContinuation.tryResume]
     * and [SelectInstance.trySelect]. When the channel becomes closed,
     * [tryResumeHasNextOnClosedChannel] should be used instead.
     */
    protected open inner class BufferedChannelIterator : ChannelIterator<E>, Waiter {
        /**
         * Stores the element retrieved by [hasNext] or
         * a special [CHANNEL_CLOSED] token if this channel is closed.
         * If [hasNext] has not been invoked yet, [NO_RECEIVE_RESULT] is stored.
         */
        private var receiveResult: Any? = NO_RECEIVE_RESULT

        /**
         * When [hasNext] suspends, this field stores the corresponding
         * continuation. The [tryResumeHasNext] and [tryResumeHasNextOnClosedChannel]
         * function resume this continuation when the [hasNext] invocation should complete.
         */
        private var continuation: CancellableContinuation<Boolean>? = null

        // When `hasNext()` suspends, the location where the continuation
        // is stored is specified via the segment and the index in it.
        // We need this information in the cancellation handler below.
        private var segment: ChannelSegment<E>? = null
        private var index = -1

        // `hasNext()` is just a special receive operation.
        override suspend fun hasNext(): Boolean =
            TODO()

        private fun onClosedHasNext(): Boolean {
            this.receiveResult = CHANNEL_CLOSED
            onReceiveSynchronizationCompleted()
            val cause = closeCause ?: return false
            throw recoverStackTrace(cause)
        }

        private fun onClosedHasNextNoWaiterSuspend() {
            // Read the current continuation and clean
            // the corresponding field to avoid memory leaks.
            val cont = this.continuation!!
            this.continuation = null
            // Update the `hasNext()` internal result and inform
            // `BufferedChannel` extensions that synchronization
            // of this receive operation is completed.
            this.receiveResult = CHANNEL_CLOSED
            onReceiveSynchronizationCompleted()
            // If this channel was closed without exception,
            // `hasNext()` should return `false`; otherwise,
            // it throws the closing exception.
            val cause = closeCause
            if (cause == null) {
                cont.resume(false)
            } else {
                cont.resumeWithException(recoverStackTrace(cause, cont))
            }
        }

        @Suppress("UNCHECKED_CAST")
        override fun next(): E {
            // Read the already received result, or [NO_RECEIVE_RESULT] if [hasNext] has not been invoked yet.
            val result = receiveResult
            check(result !== NO_RECEIVE_RESULT) { "`hasNext()` has not been invoked" }
            receiveResult = NO_RECEIVE_RESULT
            // Is this channel closed?
            if (result === CHANNEL_CLOSED) throw recoverStackTrace(receiveException)
            // Return the element.
            return result as E
        }

        private fun tryResumeHasNext(element: E): Boolean {
            // Read the current continuation and clean
            // the corresponding field to avoid memory leaks.
            val cont = this.continuation!!
            this.continuation = null
            // Store the retrieved element in `receiveResult`.
            this.receiveResult = element
            // Try to resume this `hasNext()`. Importantly, the receiver coroutine
            // may be cancelled after it is successfully resumed but not dispatched yet.
            // In case `onUndeliveredElement` is specified, we need to invoke it in the latter case.
            return cont.tryResume0(true, onUndeliveredElement?.bindCancellationFun(element, cont.context))
        }

        fun tryResumeHasNextOnClosedChannel() {
            // Read the current continuation and clean
            // the corresponding field to avoid memory leaks.
            val cont = this.continuation!!
            this.continuation = null
            // Update the `hasNext()` internal result and inform
            // `BufferedChannel` extensions that synchronization
            // of this receive operation is completed.
            this.receiveResult = CHANNEL_CLOSED
            // If this channel was closed without exception,
            // `hasNext()` should return `false`; otherwise,
            // it throws the closing exception.
            val cause = closeCause
            if (cause == null) {
                cont.resume(false)
            } else {
                cont.resumeWithException(recoverStackTrace(cause, cont))
            }
        }
    }

    // ##############################
    // ## Closing and Cancellation ##
    // ##############################

    /**
     * Store the cause of closing this channel, either via [close] or [cancel] call.
     * The closing cause can be set only once.
     */
    private val _closeCause = atomic<Any?>(NO_CLOSE_CAUSE)
    // Should be called only if this channel is closed or cancelled.
    protected val closeCause get() = _closeCause.value as Throwable?

    /** Returns the closing cause if it is non-null, or [ClosedSendChannelException] otherwise. */
    protected val sendException get() = closeCause ?: ClosedSendChannelException(DEFAULT_CLOSE_MESSAGE)

    /** Returns the closing cause if it is non-null, or [ClosedReceiveChannelException] otherwise. */
    private val receiveException get() = closeCause ?: ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)

    /**
      Stores the closed handler installed by [invokeOnClose].
      To synchronize [invokeOnClose] and [close], two additional
      marker states, [CLOSE_HANDLER_INVOKED] and [CLOSE_HANDLER_CLOSED]
      are used. The resulting state diagram is presented below.

      +------+  install handler  +---------+  close(..)  +---------+
      | null |------------------>| handler |------------>| INVOKED |
      +------+                   +---------+             +---------+
         |
         | close(..)  +--------+
         +----------->| CLOSED |
                      +--------+
     */
    private val closeHandler = atomic<Any?>(null)

    /**
     * Invoked when channel is closed as the last action of [close] invocation.
     * This method should be idempotent and can be called multiple times.
     */
    protected open fun onClosedIdempotent() {}

    override fun close(cause: Throwable?): Boolean =
        closeOrCancelImpl(cause, cancel = false)

    @Suppress("OVERRIDE_DEPRECATION")
    final override fun cancel(cause: Throwable?): Boolean = cancelImpl(cause)

    @Suppress("OVERRIDE_DEPRECATION")
    final override fun cancel() { cancelImpl(null) }

    final override fun cancel(cause: CancellationException?) { cancelImpl(cause) }

    internal open fun cancelImpl(cause: Throwable?): Boolean =
        closeOrCancelImpl(cause ?: CancellationException("Channel was cancelled"), cancel = true)

    /**
     * This is a common implementation for [close] and [cancel]. It first tries
     * to install the specified cause; the invocation that successfully installs
     * the cause returns `true` as a results of this function, while all further
     * [close] and [cancel] calls return `false`.
     *
     * After the closing/cancellation cause is installed, the channel should be marked
     * as closed or cancelled, which bounds further `send(e)`-s to fails.
     *
     * Then, [completeCloseOrCancel] is called, which cancels waiting `receive()`
     * requests ([cancelSuspendedReceiveRequests]) and removes unprocessed elements
     * ([removeUnprocessedElements]) in case this channel is cancelled.
     *
     * Finally, if this [closeOrCancelImpl] has installed the cause, therefore,
     * has closed the channel, [closeHandler] and [onClosedIdempotent] should be invoked.
     */
    protected open fun closeOrCancelImpl(cause: Throwable?, cancel: Boolean): Boolean {
        // If this is a `cancel(..)` invocation, set a bit that the cancellation
        // has been started. This is crucial for ensuring linearizability,
        // when concurrent `close(..)` and `isClosedFor[Send,Receive]` operations
        // help this `cancel(..)`.
        if (cancel) markCancellationStarted()
        // Try to install the specified cause. On success, this invocation will
        // return `true` as a result; otherwise, it will complete with `false`.
        val closedByThisOperation = _closeCause.compareAndSet(NO_CLOSE_CAUSE, cause)
        // Mark this channel as closed or cancelled, depending on this operation type.
        if (cancel) markCancelled() else markClosed()
        // Complete the closing or cancellation procedure.
        completeCloseOrCancel()
        // Finally, if this operation has installed the cause,
        // it should invoke the close handlers.
        return closedByThisOperation.also {
            onClosedIdempotent()
            if (it) invokeCloseHandler()
        }
    }

    /**
     * Invokes the installed close handler,
     * updating the [closeHandler] state correspondingly.
     */
    private fun invokeCloseHandler() {
        val closeHandler = closeHandler.getAndUpdate {
            if (it === null) {
                // Inform concurrent `invokeOnClose`
                // that this channel is already closed.
                CLOSE_HANDLER_CLOSED
            } else {
                // Replace the handler with a special
                // `INVOKED` marker to avoid memory leaks.
                CLOSE_HANDLER_INVOKED
            }
        } ?: return // no handler was installed, finish.
        // Invoke the handler.
        @Suppress("UNCHECKED_CAST")
        closeHandler as (cause: Throwable?) -> Unit
        closeHandler(closeCause)
    }

    override fun invokeOnClose(handler: (cause: Throwable?) -> Unit) {
        // Try to install the handler, finishing on success.
        if (closeHandler.compareAndSet(null, handler)) {
            // Handler has been successfully set, finish the operation.
            return
        }
        // Either another handler is already set, or this channel is closed.
        // In the latter case, the current handler should be invoked.
        // However, the implementation must ensure that at most one
        // handler is called, throwing an `IllegalStateException`
        // if another close handler has been invoked.
        closeHandler.loop { cur ->
            when {
                cur === CLOSE_HANDLER_CLOSED -> {
                    // Try to update the state from `CLOSED` to `INVOKED`.
                    // This is crucial to guarantee that at most one handler can be called.
                    // On success, invoke the handler and finish.
                    if (closeHandler.compareAndSet(CLOSE_HANDLER_CLOSED, CLOSE_HANDLER_INVOKED)) {
                        handler(closeCause)
                        return
                    }
                }
                cur === CLOSE_HANDLER_INVOKED -> error("Another handler was already registered and successfully invoked")
                else -> error("Another handler is already registered: $cur")
            }
        }
    }

    /**
     * Marks this channel as closed.
     * In case [cancelImpl] has already been invoked,
     * and this channel is marked with [CLOSE_STATUS_CANCELLATION_STARTED],
     * this function marks the channel as cancelled.
     *
     * All operation that notice this channel in the closed state,
     * must help to complete the closing via [completeCloseOrCancel].
     */
    private fun markClosed(): Unit =
        closed.update { cur ->
            when (cur) {
                CLOSE_STATUS_ACTIVE -> CLOSE_STATUS_CLOSED // the channel is neither closed nor cancelled
                CLOSE_STATUS_CANCELLATION_STARTED -> CLOSE_STATUS_CANCELLED // the channel is going to be cancelled
                else -> return // the channel is already marked as closed or cancelled.
            }
        }

    /**
     * Marks this channel as cancelled.
     *
     * All operation that notice this channel in the cancelled state,
     * must help to complete the cancellation via [completeCloseOrCancel].
     */
    private fun markCancelled(): Unit {
        closed.value - CLOSE_STATUS_CANCELLED
    }

    /**
     * When the cancellation procedure starts, it is critical
     * to mark the closing status correspondingly. Thus, other
     * operations, which may help to complete the cancellation,
     * always correctly update the status to `CANCELLED`.
     */
    private fun markCancellationStarted(): Unit =
        closed.update { cur ->
            if (cur == CLOSE_STATUS_ACTIVE) CLOSE_STATUS_CANCELLATION_STARTED
            else return // this channel is already closed or cancelled
        }

    /**
     * Completes the started [close] or [cancel] procedure.
     */
    private fun completeCloseOrCancel() {
        isClosedForSendImpl // must finish the started close/cancel if one is detected.
    }

    /**
     * Completes the channel closing procedure.
     */
    private fun completeClose(): ChannelSegment<E> {
        // Close the linked list for further segment addition,
        // obtaining the last segment in the data structure.
        val lastSegment = closeLinkedList()
        // Resume waiting `receive()` requests,
        // informing them that the channel is closed.
        cancelSuspendedReceiveRequests()
        // Return the last segment in the linked list as a result
        // of this function; we need it in `completeCancel(..)`.
        return lastSegment
    }

    /**
     * Completes the channel cancellation procedure.
     */
    private fun completeCancel() {
        // First, ensure that this channel is closed,
        // obtaining the last segment in the linked list.
        completeClose()
        // Cancel suspended `send(e)` requests and
        // remove buffered elements in the reverse order.
        removeUnprocessedElements()
    }

    /**
     * Closes the underlying linked list of segments for further segment addition.
     */
    private fun closeLinkedList(): ChannelSegment<E> {
        // Close the linked list of segment for new segment addition
        // and return the last segment in the linked list.
        return enqSegment.value.close()
    }

    /**
     * Cancels suspended `send(e)` requests and removes buffered elements
     * starting from the last cell in the specified [lastSegment] (it must
     * be the physical tail of the underlying linked list) and updating
     * the cells in reverse order.
     */
    private fun removeUnprocessedElements() {
        TODO()
    }

    /**
     * Cancels suspended `receive` requests from the end to the beginning,
     * also moving empty cells to the `CHANNEL_CLOSED` state.
     */
    private fun cancelSuspendedReceiveRequests() {
        TODO()
    }

    /**
     * Resumes this receiver because this channel is closed.
     * This function does not take any effect if the operation has already been resumed or cancelled.
     */
    private fun Waiter.resumeReceiverOnClosedChannel() = resumeWaiterOnClosedChannel(receiver = true)

    /**
     * Resumes this sender because this channel is cancelled.
     * This function does not take any effect if the operation has already been resumed or cancelled.
     */
    private fun Waiter.resumeSenderOnCancelledChannel() = resumeWaiterOnClosedChannel(receiver = false)

    private fun Waiter.resumeWaiterOnClosedChannel(receiver: Boolean) {
        when (this) {
            is CancellableContinuation<*> -> resumeWithException(if (receiver) receiveException else sendException)
            is ReceiveCatching<*> -> cont.resume(closed(closeCause))
            is BufferedChannel<*>.BufferedChannelIterator -> tryResumeHasNextOnClosedChannel()
            is SelectInstance<*> -> trySelect(this@BufferedChannel, CHANNEL_CLOSED)
            else -> error("Unexpected waiter: $this")
        }
    }

    @ExperimentalCoroutinesApi
    override val isClosedForSend: Boolean
        get() = isClosedForSendImpl

    private val isClosedForSendImpl: Boolean
        get() = closed.value.isClosedForSend0

    private val Int.isClosedForSend0 get() =
        isClosed(this, isClosedForReceive = false)

    @ExperimentalCoroutinesApi
    override val isClosedForReceive: Boolean
        get() = isClosedForReceiveImpl

    private val isClosedForReceiveImpl: Boolean
        get() = closed.value.isClosedForReceive0

    private val Int.isClosedForReceive0 get() =
        isClosed(this, isClosedForReceive = true)

    private fun isClosed(
        closeStatusCur: Int,
        isClosedForReceive: Boolean
    ) = when (closeStatusCur) {
        // This channel is active and has not been closed.
        CLOSE_STATUS_ACTIVE -> false
        // The cancellation procedure has been started but
        // not linearized yet, so this channel should be
        // considered as active.
        CLOSE_STATUS_CANCELLATION_STARTED -> false
        // This channel has been successfully closed.
        // Help to complete the closing procedure to
        // guarantee linearizability, and return `true`
        // for senders or the flag whether there still
        // exist elements to retrieve for receivers.
        CLOSE_STATUS_CLOSED -> {
            completeClose()
            // When `isClosedForReceive` is `false`, always return `true`.
            // Otherwise, it is possible that the channel is closed but
            // still has elements to retrieve.
            if (isClosedForReceive) !hasElements() else true
        }
        // This channel has been successfully cancelled.
        // Help to complete the cancellation procedure to
        // guarantee linearizability and return `true`.
        CLOSE_STATUS_CANCELLED -> {
            completeCancel()
            true
        }
        else -> error("unexpected close status: ${closeStatusCur}")
    }

    @ExperimentalCoroutinesApi
    override val isEmpty: Boolean get() {
        // This function should return `false` if
        // this channel is closed for `receive`.
        if (isClosedForReceiveImpl) return false
        // Does this channel has elements to retrieve?
        if (hasElements()) return false
        // This channel does not have elements to retrieve;
        // Check that it is still not closed for `receive`.
        return !isClosedForReceiveImpl
    }

    internal fun hasElements(): Boolean = TODO()

    private fun findSegmentEnq(id: Long, startFrom: ChannelSegment<E>): ChannelSegment<E> =
        enqSegment.findSegmentAndMoveForward(id, startFrom, ::createSegment).segment

    private fun findSegmentDeq(id: Long, startFrom: ChannelSegment<E>): ChannelSegment<E> =
        deqSegment.findSegmentAndMoveForward(id, startFrom, ::createSegment).segment.also { it.cleanPrev() }

    // This is an internal methods for tests.
    fun checkSegmentStructureInvariants() {
    }
}

/**
 * The channel is represented as a list of segments, which simulates an infinite array.
 * Each segment has its own [id], which increase from the beginning. These [id]s help
 * to update [BufferedChannel.sendSegment], [BufferedChannel.receiveSegment],
 * and [BufferedChannel.bufferEndSegment] correctly.
 */
internal class ChannelSegment<E>(id: Long, prev: ChannelSegment<E>?, pointers: Int) : Segment<ChannelSegment<E>>(id, prev, pointers) {
    private val data = atomicArrayOfNulls<Any?>(SEGMENT_SIZE)
    override val numberOfSlots: Int get() = SEGMENT_SIZE

    internal fun get(index: Int): Any? = data[index].value

    internal fun set(index: Int, value: Any?) {
        data[index].value = value
    }

    internal fun lazySet(index: Int, value: Any?) {
        data[index].lazySet(value)
    }

    internal fun cas(index: Int, from: Any?, to: Any?) = data[index].compareAndSet(from, to)

    internal fun getAndSet(index: Int, update: Any?) = data[index].getAndSet(update)
}
private fun <E> createSegment(id: Long, prev: ChannelSegment<E>) = ChannelSegment(
    id = id,
    prev = prev,
    pointers = 0
)

/**
 * Number of cells in each segment.
 */
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.bufferedChannel.segmentSize", 64)

/**
 * Tries to resume this continuation with the specified
 * value. Returns `true` on success and `false` on failure.
 */
private fun <T> CancellableContinuation<T>.tryResume0(
    value: T,
    onCancellation: ((cause: Throwable) -> Unit)? = null
): Boolean =
    tryResume(value, null, onCancellation).let { token ->
        if (token != null) {
            completeResume(token)
            true
        } else false
    }

/*
  Cell states. The initial "empty" state is represented with `null`,
  and suspended operations are represented with [Waiter] instances.
 */
private val POISONED = Symbol("POISONED")
private val DONE = Symbol("DONE")
internal val CHANNEL_CLOSED = Symbol("CHANNEL_CLOSED")



/**
 * To distinguish suspended [BufferedChannel.receive] and
 * [BufferedChannel.receiveCatching] operations, the latter
 * uses this wrapper for its continuation.
 */
private class ReceiveCatching<E>(
    @JvmField val cont: CancellableContinuation<ChannelResult<E>>
) : Waiter


/**
 * Special value for [BufferedChannel.BufferedChannelIterator.receiveResult]
 * that indicates the absence of pre-received result.
 */
private val NO_RECEIVE_RESULT = Symbol("NO_RECEIVE_RESULT")

/*
  As [BufferedChannel.invokeOnClose] can be invoked concurrently
  with channel closing, we have to synchronize them. These two
  markers help with the synchronization.
 */
private val CLOSE_HANDLER_CLOSED = Symbol("CLOSE_HANDLER_CLOSED")
private val CLOSE_HANDLER_INVOKED = Symbol("CLOSE_HANDLER_INVOKED")

/**
 * Specifies the absence of closing cause, stored in [BufferedChannel._closeCause].
 * When the channel is closed or cancelled without exception, this [NO_CLOSE_CAUSE]
 * marker should be replaced with `null`.
 */
private val NO_CLOSE_CAUSE = Symbol("NO_CLOSE_CAUSE")

/*
  The channel close statuses. The transition scheme is the following:
    +--------+   +----------------------+   +-----------+
    | ACTIVE |-->| CANCELLATION_STARTED |-->| CANCELLED |
    +--------+   +----------------------+   +-----------+
        |                                         ^
        |             +--------+                  |
        +------------>| CLOSED |------------------+
                      +--------+
  We need `CANCELLATION_STARTED` to synchronize
  concurrent closing and cancellation.
 */
private const val CLOSE_STATUS_ACTIVE = 0
private const val CLOSE_STATUS_CANCELLATION_STARTED = 1
private const val CLOSE_STATUS_CLOSED = 2
private const val CLOSE_STATUS_CANCELLED = 3

/**
 * All waiters, such as [CancellableContinuationImpl], [SelectInstance], and
 * [BufferedChannel.BufferedChannelIterator], should be marked with this interface
 * to make the code faster and easier to read.
 */
internal interface Waiter
