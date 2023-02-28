@file:Suppress("PrivatePropertyName")

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.ChannelResult.Companion.closed
import kotlinx.coroutines.channels.ChannelResult.Companion.failure
import kotlinx.coroutines.channels.ChannelResult.Companion.success
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.selects.TrySelectDetailedResult.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.js.*
import kotlin.jvm.*
import kotlin.math.*
import kotlin.random.*
import kotlin.reflect.*

/**
 * The buffered channel implementation, which also serves as a rendezvous channel when the capacity is zero.
 * The high-level structure bases on a conceptually infinite array for storing elements and waiting requests,
 * separate counters of [send] and [receive] invocations that were ever performed, and an additional counter
 * that indicates the end of the logical buffer by counting the number of array cells it ever contained.
 * The key idea is that both [send] and [receive] start by incrementing their counters, assigning the array cell
 * referenced by the counter. In case of rendezvous channels, the operation either suspends and stores its continuation
 * in the cell or makes a rendezvous with the opposite request. Each cell can be processed by exactly one [send] and
 * one [receive]. As for buffered channels, [send]-s can also add elements without suspension if the logical buffer
 * contains the cell, while the [receive] operation updates the end of the buffer when its synchronization finishes.
 *
 * Please see the ["Fast and Scalable Channels in Kotlin Coroutines"](https://arxiv.org/abs/2211.04986)
 * paper by Nikita Koval, Roman Elizarov, and Dan Alistarh for the detailed algorithm description.
 */
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

    // Maintenance note: use `Buffered1ChannelLincheckTest` to check hypotheses.

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
    private val sendersAndCloseStatus = atomic(0L)
    private val receivers = atomic(0L)
    private val bufferEnd = atomic(initialBufferEnd(capacity))

    internal val sendersCounter: Long get() = sendersAndCloseStatus.value.sendersCounter
    internal val receiversCounter: Long get() = receivers.value
    private val bufferEndCounter: Long get() = bufferEnd.value

    /*
      Additionally to the counters above, we need an extra one that
      tracks the number of cells processed by `expandBuffer()`.
      When a receiver aborts, the corresponding cell might be
      physically removed from the data structure to avoid memory
      leaks, while it still can be unprocessed by `expandBuffer()`.
      In this case, `expandBuffer()` cannot know whether the
      removed cell contained sender or receiver and, therefore,
      cannot proceed. To solve the race, we ensure that cells
      correspond to cancelled receivers cannot be physically
      removed until the cell is processed.
      This additional counter enables the synchronization,
     */
    private val completedExpandBuffersAndPauseFlag = atomic(bufferEndCounter)

    private val isRendezvousOrUnlimited
        get() = bufferEndCounter.let { it == BUFFER_END_RENDEZVOUS || it == BUFFER_END_UNLIMITED }

    private val sendSegment: AtomicRef<ChannelSegment<E>>
    private val receiveSegment: AtomicRef<ChannelSegment<E>>
    private val bufferEndSegment: AtomicRef<ChannelSegment<E>>

    init {
        @Suppress("LeakingThis")
        val firstSegment = ChannelSegment(id = 0, prev = null, channel = this, pointers = 3)
        sendSegment = atomic(firstSegment)
        receiveSegment = atomic(firstSegment)
        // If this channel is rendezvous or has unlimited capacity, the algorithm never
        // invokes the buffer expansion procedure, and the corresponding segment reference
        // points to a special `NULL_SEGMENT` one and never updates.
        @Suppress("UNCHECKED_CAST")
        bufferEndSegment = atomic(if (isRendezvousOrUnlimited) (NULL_SEGMENT as ChannelSegment<E>) else firstSegment)
    }

    // #########################
    // ## The send operations ##
    // #########################

    override suspend fun send(element: E): Unit =
        sendImpl( // <-- this is an inline function
            element = element,
            // Do not create a continuation until it is required;
            // it is created later via [onNoWaiterSuspend], if needed.
            waiter = null,
            // Finish immediately if a rendezvous happens
            // or the element has been buffered.
            onRendezvousOrBuffered = {},
            // As no waiter is provided, suspension is impossible.
            onSuspend = { _, _ -> assert { false } },
            // According to the `send(e)` contract, we need to call
            // `onUndeliveredElement(..)` handler and throw an exception
            // if the channel is already closed.
            onClosed = { onClosedSend(element) },
            // When `send(e)` decides to suspend, the corresponding
            // `onNoWaiterSuspend` function that creates a continuation
            // is called. The tail-call optimization is applied here.
            onNoWaiterSuspend = { segm, i, elem, s -> sendOnNoWaiterSuspend(segm, i, elem, s) }
        )

    // NB: return type could've been Nothing, but it breaks TCO
    private suspend fun onClosedSend(element: E): Unit = suspendCancellableCoroutine { continuation ->
        onUndeliveredElement?.callUndeliveredElementCatchingException(element)?.let {
            // If it crashes, add send exception as suppressed for better diagnostics
            it.addSuppressed(sendException)
            continuation.resumeWithStackTrace(it)
            return@suspendCancellableCoroutine
        }
        continuation.resumeWithStackTrace(sendException)
    }

    private suspend fun sendOnNoWaiterSuspend(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int,
        /** The element to be inserted. */
        element: E,
        /** The global index of the cell. */
        s: Long
    ) = suspendCancellableCoroutineReusable sc@{ cont ->
        sendImplOnNoWaiter( // <-- this is an inline function
            segment = segment, index = index, element = element, s = s,
            // Store the created continuation as a waiter.
            waiter = cont,
            // If a rendezvous happens or the element has been buffered,
            // resume the continuation and finish. In case of prompt
            // cancellation, it is guaranteed that the element
            // has been already buffered or passed to receiver.
            onRendezvousOrBuffered = { cont.resume(Unit) },
            // If the channel is closed, call `onUndeliveredElement(..)` and complete the
            // continuation with the corresponding exception.
            onClosed = { onClosedSendOnNoWaiterSuspend(element, cont) },
        )
    }

    private fun Waiter.prepareSenderForSuspension(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int
    ) {
        if (onUndeliveredElement == null) {
            invokeOnCancellation(segment, index)
        } else {
            when (this) {
                is CancellableContinuation<*> -> {
                    invokeOnCancellation(SenderWithOnUndeliveredElementCancellationHandler(segment, index, context).asHandler)
                }
                is SelectInstance<*> -> {
                    disposeOnCompletion(SenderWithOnUndeliveredElementCancellationHandler(segment, index, context))
                }
                is SendBroadcast -> {
                    cont.invokeOnCancellation(SenderWithOnUndeliveredElementCancellationHandler(segment, index, cont.context).asHandler)
                }
                else -> error("unexpected sender: $this")
            }
        }
    }

    private inner class SenderWithOnUndeliveredElementCancellationHandler(
        private val segment: ChannelSegment<E>,
        private val index: Int,
        private val context: CoroutineContext
    ) : BeforeResumeCancelHandler(), DisposableHandle {
        override fun dispose() {
            segment.onSenderCancellationWithOnUndeliveredElement(index, context)
        }

        override fun invoke(cause: Throwable?) = dispose()
    }

    private fun onClosedSendOnNoWaiterSuspend(element: E, cont: CancellableContinuation<Unit>) {
        onUndeliveredElement?.callUndeliveredElement(element, cont.context)
        cont.resumeWithException(recoverStackTrace(sendException, cont))
    }

    override fun trySend(element: E): ChannelResult<Unit> {
        // Do not try to send the element if the plain `send(e)` operation would suspend.
        if (shouldSendSuspend(sendersAndCloseStatus.value)) return failure()
        // This channel either has waiting receivers or is closed.
        // Let's try to send the element!
        // The logic is similar to the plain `send(e)` operation, with
        // the only difference that we install `INTERRUPTED_SEND` in case
        // the operation decides to suspend.
        return sendImpl( // <-- this is an inline function
            element = element,
            // Store an already interrupted sender in case of suspension.
            waiter = INTERRUPTED_SEND,
            // Finish successfully when a rendezvous happens
            // or the element has been buffered.
            onRendezvousOrBuffered = { success(Unit) },
            // On suspension, the `INTERRUPTED_SEND` token has been installed,
            // and this `trySend(e)` must fail. According to the contract,
            // we do not need to call the [onUndeliveredElement] handler.
            onSuspend = { segm, _ ->
                segm.onSlotCleaned()
                failure()
            },
            // If the channel is closed, return the corresponding result.
            onClosed = { closed(sendException) }
        )
    }

    /**
     * This is a special `send(e)` implementation that returns `true` if the element
     * has been successfully sent, and `false` if the channel is closed.
     *
     * In case of coroutine cancellation, the element may be undelivered --
     * the [onUndeliveredElement] feature is unsupported in this implementation.
     *
     * Note that this implementation always invokes [suspendCancellableCoroutineReusable],
     * as we do not care about broadcasts performance -- they are already deprecated.
     */
    internal open suspend fun sendBroadcast(element: E): Boolean = suspendCancellableCoroutineReusable { cont ->
        check(onUndeliveredElement == null) {
            "the `onUndeliveredElement` feature is unsupported for `sendBroadcast(e)`"
        }
        sendImpl(
            element = element,
            waiter = SendBroadcast(cont),
            onRendezvousOrBuffered = { cont.resume(true) },
            onSuspend = { _, _ -> },
            onClosed = { cont.resume(false) }
        )
    }

    /**
     * Specifies waiting [sendBroadcast] operation.
     */
    private class SendBroadcast(
        val cont: CancellableContinuation<Boolean>
    ) : Waiter by cont as CancellableContinuationImpl<Boolean>

    /**
     * Abstract send implementation.
     */
    protected inline fun <R> sendImpl(
        /* The element to be sent. */
        element: E,
        /* The waiter to be stored in case of suspension,
        or `null` if the waiter is not created yet.
        In the latter case, when the algorithm decides
        to suspend, [onNoWaiterSuspend] is called. */
        waiter: Any?,
        /* This lambda is invoked when the element has been
        buffered or a rendezvous with a receiver happens. */
        onRendezvousOrBuffered: () -> R,
        /* This lambda is called when the operation suspends in the
        cell specified by the segment and the index in it. */
        onSuspend: (segm: ChannelSegment<E>, i: Int) -> R,
        /* This lambda is called when the channel
        is observed in the closed state. */
        onClosed: () -> R,
        /* This lambda is called when the operation decides
        to suspend, but the waiter is not provided (equals `null`).
        It should create a waiter and delegate to `sendImplOnNoWaiter`. */
        onNoWaiterSuspend: (
            segm: ChannelSegment<E>,
            i: Int,
            element: E,
            s: Long
        ) -> R = { _, _, _, _ -> error("unexpected") }
    ): R {
        // Read the segment reference before the counter increment;
        // it is crucial to be able to find the required segment later.
        var segment = sendSegment.value
        while (true) {
            // Atomically increment the `senders` counter and obtain the
            // value right before the increment along with the close status.
            val sendersAndCloseStatusCur = sendersAndCloseStatus.getAndIncrement()
            val s = sendersAndCloseStatusCur.sendersCounter
            // Is this channel already closed? Keep the information.
            val closed = sendersAndCloseStatusCur.isClosedForSend0
            // Count the required segment id and the cell index in it.
            val id = s / SEGMENT_SIZE
            val i = (s % SEGMENT_SIZE).toInt()
            // Try to find the required segment if the initially obtained
            // one (in the beginning of this function) has lower id.
            if (segment.id != id) {
                // Find the required segment.
                segment = findSegmentSend(id, segment) ?:
                    // The required segment has not been found.
                    // Finish immediately if this channel is closed,
                    // restarting the operation otherwise.
                    // In the latter case, the required segment was full
                    // of interrupted waiters and, therefore, removed
                    // physically to avoid memory leaks.
                    if (closed) {
                        return onClosed()
                    } else {
                        continue
                    }
            }
            // Update the cell according to the algorithm. Importantly, when
            // the channel is already closed, storing a waiter is illegal, so
            // the algorithm stores the `INTERRUPTED_SEND` token in this case.
            when (updateCellSend(segment, i, element, s, waiter, closed)) {
                RESULT_RENDEZVOUS -> {
                    // A rendezvous with a receiver has happened.
                    // The previous segments are no longer needed
                    // for the upcoming requests, so the algorithm
                    // resets the link to the previous segment.
                    segment.cleanPrev()
                    return onRendezvousOrBuffered()
                }
                RESULT_BUFFERED -> {
                    // The element has been buffered.
                    return onRendezvousOrBuffered()
                }
                RESULT_SUSPEND -> {
                    // The operation has decided to suspend and installed the
                    // specified waiter. If the channel was already closed,
                    // and the `INTERRUPTED_SEND` token has been installed as a waiter,
                    // this request finishes with the `onClosed()` action.
                    if (closed) {
                        segment.onSlotCleaned()
                        return onClosed()
                    }
                    (waiter as? Waiter)?.prepareSenderForSuspension(segment, i)
                    return onSuspend(segment, i)
                }
                RESULT_CLOSED -> {
                    // This channel is closed.
                    // In case this segment is already or going to be
                    // processed by a receiver, ensure that all the
                    // previous segments are unreachable.
                    if (s < receiversCounter) segment.cleanPrev()
                    return onClosed()
                }
                RESULT_FAILED -> {
                    // Either the cell stores an interrupted receiver,
                    // or it was poisoned by a concurrent receiver.
                    // In both cases, all the previous segments are already processed,
                    segment.cleanPrev()
                    continue
                }
                RESULT_SUSPEND_NO_WAITER -> {
                    // The operation has decided to suspend,
                    // but no waiter has been provided.
                    return onNoWaiterSuspend(segment, i, element, s)
                }
            }
        }
    }

    private inline fun sendImplOnNoWaiter(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int,
        /* The element to be sent. */
        element: E,
        /* The global index of the cell. */
        s: Long,
        /* The waiter to be stored in case of suspension. */
        waiter: Waiter,
        /* This lambda is invoked when the element has been
        buffered or a rendezvous with a receiver happens.*/
        onRendezvousOrBuffered: () -> Unit,
        /* This lambda is called when the channel
        is observed in the closed state. */
        onClosed: () -> Unit,
    ) {
        // Update the cell again, now with the non-null waiter,
        // restarting the operation from the beginning on failure.
        // Check the `sendImpl(..)` function for the comments.
        when (updateCellSend(segment, index, element, s, waiter, false)) {
            RESULT_RENDEZVOUS -> {
                segment.cleanPrev()
                onRendezvousOrBuffered()
            }
            RESULT_BUFFERED -> {
                onRendezvousOrBuffered()
            }
            RESULT_SUSPEND -> {
                waiter.prepareSenderForSuspension(segment, index)
            }
            RESULT_CLOSED -> {
                if (s < receiversCounter) segment.cleanPrev()
                onClosed()
            }
            RESULT_FAILED -> {
                segment.cleanPrev()
                sendImpl(
                    element = element,
                    waiter = waiter,
                    onRendezvousOrBuffered = onRendezvousOrBuffered,
                    onSuspend = { _, _ -> },
                    onClosed = onClosed,
                )
            }
            else -> error("unexpected")
        }
    }

    private fun updateCellSend(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int,
        /* The element to be sent. */
        element: E,
        /* The global index of the cell. */
        s: Long,
        /* The waiter to be stored in case of suspension. */
        waiter: Any?,
        closed: Boolean
    ): Int {
        // This is a fast-path of `updateCellSendSlow(..)`.
        //
        // First, the algorithm stores the element,
        // performing the synchronization after that.
        // This way, receivers safely retrieve the
        // element, following the safe publication pattern.
        segment.storeElement(index, element)
        if (closed) return updateCellSendSlow(segment, index, element, s, waiter, closed)
        // Read the current cell state.
        val state = segment.getState(index)
        when {
            // The cell is empty.
            state === null -> {
                // If the element should be buffered, or a rendezvous should happen
                // while the receiver is still coming, try to buffer the element.
                // Otherwise, try to store the specified waiter in the cell.
                if (bufferOrRendezvousSend(s)) {
                    // Move the cell state to `BUFFERED`.
                    if (segment.casState(index, null, BUFFERED)) {
                        // The element has been successfully buffered, finish.
                        return RESULT_BUFFERED
                    }
                } else {
                    // This `send(e)` operation should suspend.
                    // However, in case the channel has already
                    // been observed closed, `INTERRUPTED_SEND`
                    // is installed instead.
                    if (waiter == null) {
                        // The waiter is not specified; return the corresponding result.
                        return RESULT_SUSPEND_NO_WAITER
                    } else {
                        // Try to install the waiter.
                        if (segment.casState(index, null, waiter)) return RESULT_SUSPEND
                    }
                }
            }
            // A waiting receiver is stored in the cell.
            state is Waiter -> {
                // As the element will be passed directly to the waiter,
                // the algorithm cleans the element slot in the cell.
                segment.cleanElement(index)
                // Try to make a rendezvous with the suspended receiver.
                return if (state.tryResumeReceiver(element)) {
                    // Rendezvous! Move the cell state to `DONE_RCV` and finish.
                    segment.setState(index, DONE_RCV)
                    onReceiveDequeued()
                    RESULT_RENDEZVOUS
                } else {
                    // The resumption has failed. Update the cell state correspondingly
                    // and clean the element field. It is also possible for a concurrent
                    // cancellation handler to update the cell state; we can safely
                    // ignore these updates.
                    if (segment.getAndSetState(index, INTERRUPTED_RCV) !== INTERRUPTED_RCV) {
                        segment.onCancelledRequest(index, true)
                    }
                    RESULT_FAILED
                }
            }
        }
        return updateCellSendSlow(segment, index, element, s, waiter, closed)
    }

    /**
     * Updates the working cell of an abstract send operation.
     */
    private fun updateCellSendSlow(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int,
        /* The element to be sent. */
        element: E,
        /* The global index of the cell. */
        s: Long,
        /* The waiter to be stored in case of suspension. */
        waiter: Any?,
        closed: Boolean
    ): Int {
        // Then, the cell state should be updated according to
        // its state machine; see the paper mentioned in the very
        // beginning for the cell life-cycle and the algorithm details.
        while (true) {
            // Read the current cell state.
            val state = segment.getState(index)
            when {
                // The cell is empty.
                state === null -> {
                    // If the element should be buffered, or a rendezvous should happen
                    // while the receiver is still coming, try to buffer the element.
                    // Otherwise, try to store the specified waiter in the cell.
                    if (bufferOrRendezvousSend(s) && !closed) {
                        // Move the cell state to `BUFFERED`.
                        if (segment.casState(index, null, BUFFERED)) {
                            // The element has been successfully buffered, finish.
                            return RESULT_BUFFERED
                        }
                    } else {
                        // This `send(e)` operation should suspend.
                        // However, in case the channel has already
                        // been observed closed, `INTERRUPTED_SEND`
                        // is installed instead.
                        when {
                            // The channel is closed
                            closed -> if (segment.casState(index, null, INTERRUPTED_SEND)) {
                                segment.onCancelledRequest(index, false)
                                return RESULT_CLOSED
                            }
                            // The waiter is not specified; return the corresponding result.
                            waiter == null -> return RESULT_SUSPEND_NO_WAITER
                            // Try to install the waiter.
                            else -> if (segment.casState(index, null, waiter)) return RESULT_SUSPEND
                        }
                    }
                }
                // This cell is in the logical buffer.
                state === IN_BUFFER -> {
                    // Try to buffer the element.
                    if (segment.casState(index, state, BUFFERED)) {
                        // The element has been successfully buffered, finish.
                        return RESULT_BUFFERED
                    }
                }
                // The cell stores a cancelled receiver.
                state === INTERRUPTED_RCV -> {
                    // Clean the element slot to avoid memory leaks and finish.
                    segment.cleanElement(index)
                    return RESULT_FAILED
                }
                // The cell is poisoned by a concurrent receive.
                state === POISONED -> {
                    // Clean the element slot to avoid memory leaks and finish.
                    segment.cleanElement(index)
                    return RESULT_FAILED
                }
                // The channel is already closed.
                state === CHANNEL_CLOSED -> {
                    // Clean the element slot to avoid memory leaks,
                    // ensure that the closing/cancellation procedure
                    // has been completed, and finish.
                    segment.cleanElement(index)
                    completeCloseOrCancel()
                    return RESULT_CLOSED
                }
                // A waiting receiver is stored in the cell.
                else -> {
                    assert { state is Waiter || state is WaiterEB }
                    // As the element will be passed directly to the waiter,
                    // the algorithm cleans the element slot in the cell.
                    segment.cleanElement(index)
                    // Unwrap the waiting receiver from `WaiterEB` if needed.
                    // As a receiver is stored in the cell, the buffer expansion
                    // procedure would finish, so senders simply ignore the "EB" marker.
                    val receiver = if (state is WaiterEB) state.waiter else state
                    // Try to make a rendezvous with the suspended receiver.
                    return if (receiver.tryResumeReceiver(element)) {
                        // Rendezvous! Move the cell state to `DONE_RCV` and finish.
                        segment.setState(index, DONE_RCV)
                        onReceiveDequeued()
                        RESULT_RENDEZVOUS
                    } else {
                        // The resumption has failed. Update the cell state correspondingly
                        // and clean the element field. It is also possible for a concurrent
                        // `expandBuffer()` or the cancellation handler to update the cell state;
                        // we can safely ignore these updates as senders do not help `expandBuffer()`.
                        if (segment.getAndSetState(index, INTERRUPTED_RCV) !== INTERRUPTED_RCV) {
                            segment.onCancelledRequest(index, true)
                        }
                        RESULT_FAILED
                    }
                }
            }
        }
    }

    /**
     * Checks whether a [send] invocation is bound to suspend if it is called
     * with the specified [sendersAndCloseStatus], [receivers], and [bufferEnd]
     * values. When this channel is already closed, the function returns `false`.
     *
     * Specifically, [send] suspends if the channel is not unlimited,
     * the number of receivers is greater than then index of the working cell of the
     * potential [send] invocation, and the buffer does not cover this cell
     * in case of buffered channel.
     * When the channel is already closed, [send] does not suspend.
     */
    @JsName("shouldSendSuspend0")
    private fun shouldSendSuspend(curSendersAndCloseStatus: Long): Boolean {
        // Does not suspend if the channel is already closed.
        if (curSendersAndCloseStatus.isClosedForSend0) return false
        // Does not suspend if a rendezvous may happen or the buffer is not full.
        return !bufferOrRendezvousSend(curSendersAndCloseStatus.sendersCounter)
    }

    /**
     * Returns `true` when the specified [send] should place
     * its element to the working cell without suspension.
     */
    private fun bufferOrRendezvousSend(curSenders: Long): Boolean =
        curSenders < bufferEndCounter || curSenders < receiversCounter + capacity

    /**
     * Checks whether a [send] invocation is bound to suspend if it is called
     * with the current counter and close status values. See [shouldSendSuspend] for details.
     *
     * Note that this implementation is _false positive_ in case of rendezvous channels,
     * so it can return `false` when a [send] invocation is bound to suspend. Specifically,
     * the counter of `receive()` operations may indicate that there is a waiting receiver,
     * while it has already been cancelled, so the potential rendezvous is bound to fail.
     */
    internal open fun shouldSendSuspend(): Boolean = shouldSendSuspend(sendersAndCloseStatus.value)

    /**
     * Tries to resume this receiver with the specified [element] as a result.
     * Returns `true` on success and `false` otherwise.
     */
    @Suppress("UNCHECKED_CAST")
    private fun Any.tryResumeReceiver(element: E): Boolean = when(this) {
        is SelectInstance<*> -> { // `onReceiveXXX` select clause
            trySelect(this@BufferedChannel, element)
        }
        is ReceiveCatching<*> -> {
            this as ReceiveCatching<E>
            cont.tryResume0(success(element), onUndeliveredElement?.bindCancellationFun(element, cont.context))
        }
        is BufferedChannel<*>.BufferedChannelIterator -> {
            this as BufferedChannel<E>.BufferedChannelIterator
            tryResumeHasNext(element)
        }
        is CancellableContinuation<*> -> { // `receive()`
            this as CancellableContinuation<E>
            tryResume0(element, onUndeliveredElement?.bindCancellationFun(element, context))
        }
        else -> error("Unexpected receiver type: $this")
    }

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

    override suspend fun receive(): E =
        receiveImpl( // <-- this is an inline function
            // Do not create a continuation until it is required;
            // it is created later via [onNoWaiterSuspend], if needed.
            waiter = null,
            // Return the received element on successful retrieval from
            // the buffer or rendezvous with a suspended sender.
            // Also, inform `BufferedChannel` extensions that
            // synchronization of this receive operation is completed.
            onElementRetrieved = { element ->
                return element
            },
            // As no waiter is provided, suspension is impossible.
            onSuspend = { _, _, _ -> error("unexpected") },
            // Throw an exception if the channel is already closed.
            onClosed = { throw recoverStackTrace(receiveException) },
            // If `receive()` decides to suspend, the corresponding
            // `suspend` function that creates a continuation is called.
            // The tail-call optimization is applied here.
            onNoWaiterSuspend = { segm, i, r -> receiveOnNoWaiterSuspend(segm, i, r) }
        )

    private suspend fun receiveOnNoWaiterSuspend(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int,
        /* The global index of the cell. */
        r: Long
    ) = suspendCancellableCoroutineReusable { cont ->
        receiveImplOnNoWaiter( // <-- this is an inline function
            segment = segment, index = index, r = r,
            // Store the created continuation as a waiter.
            waiter = cont,
            // In case of successful element retrieval, resume
            // the continuation with the element and inform the
            // `BufferedChannel` extensions that the synchronization
            // is completed. Importantly, the receiver coroutine
            // may be cancelled after it is successfully resumed but
            // not dispatched yet. In case `onUndeliveredElement` is
            // specified, we need to invoke it in the latter case.
            onElementRetrieved = { element ->
                val onCancellation = onUndeliveredElement?.bindCancellationFun(element, cont.context)
                cont.resume(element, onCancellation)
            },
            onClosed = { onClosedReceiveOnNoWaiterSuspend(cont) },
        )
    }

    private fun Waiter.prepareReceiverForSuspension(segment: ChannelSegment<E>, index: Int) {
        onReceiveEnqueued()
        invokeOnCancellation(segment, index)
    }

    private fun onClosedReceiveOnNoWaiterSuspend(cont: CancellableContinuation<E>) {
        cont.resumeWithException(receiveException)
    }

    /*
    The implementation is exactly the same as of `receive()`,
    with the only difference that this function returns a `ChannelResult`
    instance and does not throw exception explicitly in case the channel
    is already closed for receiving. Please refer the plain `receive()`
    implementation for the comments.
    */
    override suspend fun receiveCatching(): ChannelResult<E> =
        receiveImpl( // <-- this is an inline function
            waiter = null,
            onElementRetrieved = { element ->
                success(element)
            },
            onSuspend = { _, _, _ -> error("unexpected") },
            onClosed = { closed(closeCause) },
            onNoWaiterSuspend = { segm, i, r -> receiveCatchingOnNoWaiterSuspend(segm, i, r) }
        )

    private suspend fun receiveCatchingOnNoWaiterSuspend(
        segment: ChannelSegment<E>,
        index: Int,
        r: Long
    ) = suspendCancellableCoroutineReusable { cont ->
        val waiter = ReceiveCatching(cont as CancellableContinuationImpl<ChannelResult<E>>)
        receiveImplOnNoWaiter(
            segment, index, r,
            waiter = waiter,
            onElementRetrieved = { element ->
                cont.resume(success(element), onUndeliveredElement?.bindCancellationFun(element, cont.context))
            },
            onClosed = { onClosedReceiveCatchingOnNoWaiterSuspend(cont) }
        )
    }

    private fun onClosedReceiveCatchingOnNoWaiterSuspend(cont: CancellableContinuation<ChannelResult<E>>) {
        cont.resume(closed(closeCause))
    }

    override fun tryReceive(): ChannelResult<E> {
        // Read the `receivers` counter first.
        val r = receivers.value
        val sendersAndCloseStatusCur = sendersAndCloseStatus.value
        // Is this channel closed for receive?
        if (sendersAndCloseStatusCur.isClosedForReceive0) {
            return closed(closeCause)
        }
        // Do not try to receive an element if the plain `receive()` operation would suspend.
        val s = sendersAndCloseStatusCur.sendersCounter
        if (r >= s) return failure()
        // Let's try to retrieve an element!
        // The logic is similar to the plain `receive()` operation, with
        // the only difference that we store `INTERRUPTED_RCV` in case
        // the operation decides to suspend. This way, we can leverage
        // the unconditional `Fetch-and-Add` instruction.
        // One may consider storing `INTERRUPTED_RCV` instead of an actual waiter
        // on suspension (a.k.a. "no elements to retrieve") as a short-cut of
        // "suspending and cancelling immediately".
        return receiveImpl( // <-- this is an inline function
            // Store an already interrupted receiver in case of suspension.
            waiter = INTERRUPTED_RCV,
            // Finish when an element is successfully retrieved.
            onElementRetrieved = { element -> success(element) },
            // On suspension, the `INTERRUPTED_RCV` token has been
            // installed, and this `tryReceive()` must fail.
            onSuspend = { segm, _, globalIndex ->
                // Emulate "cancelled" receive, thus invoking 'waitExpandBufferCompletion' manually,
                // because effectively there were no cancellation
                waitExpandBufferCompletion(globalIndex)
                segm.onSlotCleaned()
                failure()
            },
            // If the channel is closed, return the corresponding result.
            onClosed = { closed(closeCause) }
        )
    }

    /**
     * Extracts the first element from this channel until the cell with the specified
     * index is moved to the logical buffer. This is a key procedure for the _conflated_
     * channel implementation, see [ConflatedBufferedChannel] with the [BufferOverflow.DROP_OLDEST]
     * strategy on buffer overflowing.
     */
    protected fun dropFirstElementUntilTheSpecifiedCellIsInTheBuffer(globalCellIndex: Long) {
        assert { isConflatedDropOldest }
        // Read the segment reference before the counter increment;
        // it is crucial to be able to find the required segment later.
        var segment = receiveSegment.value
        while (true) {
            // Read the receivers counter to check whether the specified cell is already in the buffer
            // or should be moved to the buffer in a short time, due to the already started `receive()`.
            val r = this.receivers.value
            if (globalCellIndex < max(r + capacity, bufferEndCounter)) return
            // The cell is outside the buffer. Try to extract the first element
            // if the `receivers` counter has not been changed.
            if (!this.receivers.compareAndSet(r, r + 1)) continue
            // Count the required segment id and the cell index in it.
            val id = r / SEGMENT_SIZE
            val i = (r % SEGMENT_SIZE).toInt()
            // Try to find the required segment if the initially obtained
            // segment (in the beginning of this function) has lower id.
            if (segment.id != id) {
                // Find the required segment, restarting the operation if it has not been found.
                segment = findSegmentReceive(id, segment) ?:
                    // The required segment has not been found. It is possible that the channel is already
                    // closed for receiving, so the linked list of segments is closed as well.
                    // In the latter case, the operation will finish eventually after incrementing
                    // the `receivers` counter sufficient times. Note that it is impossible to check
                    // whether this channel is closed for receiving (we do this in `receive`),
                    // as it may call this function when helping to complete closing the channel.
                    continue
            }
            // Update the cell according to the cell life-cycle.
            val updCellResult = updateCellReceive(segment, i, r, null)
            when {
                updCellResult === FAILED -> {
                    // The cell is poisoned; restart from the beginning.
                    // To avoid memory leaks, we also need to reset
                    // the `prev` pointer of the working segment.
                    if (r < sendersCounter) segment.cleanPrev()
                }
                else -> { // element
                    // A buffered element was retrieved from the cell.
                    // Clean the reference to the previous segment.
                    segment.cleanPrev()
                    @Suppress("UNCHECKED_CAST")
                    onUndeliveredElement?.callUndeliveredElementCatchingException(updCellResult as E)?.let { throw it }
                }
            }
        }
    }

    /**
     * Abstract receive implementation.
     */
    private inline fun <R> receiveImpl(
        /* The waiter to be stored in case of suspension,
        or `null` if the waiter is not created yet.
        In the latter case, if the algorithm decides
        to suspend, [onNoWaiterSuspend] is called. */
        waiter: Any?,
        /* This lambda is invoked when an element has been
        successfully retrieved, either from the buffer or
        by making a rendezvous with a suspended sender. */
        onElementRetrieved: (element: E) -> R,
        /* This lambda is called when the operation suspends in the cell
        specified by the segment and its global and in-segment indices. */
        onSuspend: (segm: ChannelSegment<E>, i: Int, r: Long) -> R,
        /* This lambda is called when the channel is observed
        in the closed state and no waiting sender is found,
        which means that it is closed for receiving. */
        onClosed: () -> R,
        /* This lambda is called when the operation decides
        to suspend, but the waiter is not provided (equals `null`).
        It should create a waiter and delegate to `sendImplOnNoWaiter`. */
        onNoWaiterSuspend: (
            segm: ChannelSegment<E>,
            i: Int,
            r: Long
        ) -> R = { _, _, _ -> error("unexpected") }
    ): R {
        // Read the segment reference before the counter increment;
        // it is crucial to be able to find the required segment later.
        var segment = receiveSegment.value
        while (true) {
            // Similar to the `send(e)` operation, `receive()` first checks
            // whether the channel is already closed for receiving.
            if (isClosedForReceive) return onClosed()
            // Atomically increments the `receivers` counter
            // and obtain the value right before the increment.
            val r = this.receivers.getAndIncrement()
            // Count the required segment id and the cell index in it.
            val id = r / SEGMENT_SIZE
            val i = (r % SEGMENT_SIZE).toInt()
            // Try to find the required segment if the initially obtained
            // segment (in the beginning of this function) has lower id.
            if (segment.id != id) {
                // Find the required segment, restarting the operation if it has not been found.
                segment = findSegmentReceive(id, segment) ?:
                    // The required segment is not found. It is possible that the channel is already
                    // closed for receiving, so the linked list of segments is closed as well.
                    // In the latter case, the operation fails with the corresponding check at the beginning.
                    continue
            }
            // Update the cell according to the cell life-cycle.
            val updCellResult = updateCellReceive(segment, i, r, waiter)
            return when {
                updCellResult === SUSPEND -> {
                    // The operation has decided to suspend and
                    // stored the specified waiter in the cell.
                    (waiter as? Waiter)?.prepareReceiverForSuspension(segment, i)
                    onSuspend(segment, i, r)
                }
                updCellResult === FAILED -> {
                    // The operation has tried to make a rendezvous
                    // but failed: either the opposite request has
                    // already been cancelled or the cell is poisoned.
                    // Restart from the beginning in this case.
                    // To avoid memory leaks, we also need to reset
                    // the `prev` pointer of the working segment.
                    if (r < sendersCounter) segment.cleanPrev()
                    continue
                }
                updCellResult === SUSPEND_NO_WAITER -> {
                    // The operation has decided to suspend,
                    // but no waiter has been provided.
                    onNoWaiterSuspend(segment, i, r)
                }
                else -> { // element
                    // Either a buffered element was retrieved from the cell
                    // or a rendezvous with a waiting sender has happened.
                    // Clean the reference to the previous segment before finishing.
                    segment.cleanPrev()
                    @Suppress("UNCHECKED_CAST")
                    onElementRetrieved(updCellResult as E)
                }
            }
        }
    }

    private inline fun receiveImplOnNoWaiter(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int,
        /* The global index of the cell. */
        r: Long,
        /* The waiter to be stored in case of suspension. */
        waiter: Waiter,
        /* This lambda is invoked when an element has been
        successfully retrieved, either from the buffer or
        by making a rendezvous with a suspended sender. */
        onElementRetrieved: (element: E) -> Unit,
        /* This lambda is called when the channel is observed
        in the closed state and no waiting senders is found,
        which means that it is closed for receiving. */
        onClosed: () -> Unit
    ) {
        // Update the cell with the non-null waiter,
        // restarting from the beginning on failure.
        // Check the `receiveImpl(..)` function for the comments.
        val updCellResult = updateCellReceive(segment, index, r, waiter)
        when {
            updCellResult === SUSPEND -> {
                waiter.prepareReceiverForSuspension(segment, index)
            }
            updCellResult === FAILED -> {
                if (r < sendersCounter) segment.cleanPrev()
                receiveImpl(
                    waiter = waiter,
                    onElementRetrieved = onElementRetrieved,
                    onSuspend = { _, _, _ -> },
                    onClosed = onClosed
                )
            }
            else -> {
                segment.cleanPrev()
                @Suppress("UNCHECKED_CAST")
                onElementRetrieved(updCellResult as E)
            }
        }
    }

    private fun updateCellReceive(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int,
        /* The global index of the cell. */
        r: Long,
        /* The waiter to be stored in case of suspension. */
        waiter: Any?,
    ): Any? {
        // This is a fast-path of `updateCellReceiveSlow(..)`.
        //
        // Read the current cell state.
        val state = segment.getState(index)
        when {
            // The cell is empty.
            state === null -> {
                // If a rendezvous must happen, the operation does not wait
                // until the cell stores a buffered element or a suspended
                // sender, poisoning the cell and restarting instead.
                // Otherwise, try to store the specified waiter in the cell.
                val senders = sendersAndCloseStatus.value.sendersCounter
                if (r >= senders) {
                    // This `receive()` operation should suspend.
                    if (waiter === null) {
                        // The waiter is not specified;
                        // return the corresponding result.
                        return SUSPEND_NO_WAITER
                    }
                    // Try to install the waiter.
                    if (segment.casState(index, state, waiter)) {
                        // The waiter has been successfully installed.
                        // Invoke the `expandBuffer()` procedure and finish.
                        expandBuffer()
                        return SUSPEND
                    }
                }
            }
            // The cell stores a buffered element.
            state === BUFFERED -> if (segment.casState(index, state, DONE_RCV)) {
                // Retrieve the element and expand the buffer.
                expandBuffer()
                return segment.retrieveElement(index)
            }
        }
        return updateCellReceiveSlow(segment, index, r, waiter)
    }

    private fun updateCellReceiveSlow(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int,
        /* The global index of the cell. */
        r: Long,
        /* The waiter to be stored in case of suspension. */
        waiter: Any?,
    ): Any? {
        // The cell state should be updated according to  its state machine;
        // see the paper mentioned in the very beginning for the algorithm details.
        while (true) {
            // Read the current cell state.
            val state = segment.getState(index)
            when {
                // The cell is empty.
                state === null || state === IN_BUFFER -> {
                    // If a rendezvous must happen, the operation does not wait
                    // until the cell stores a buffered element or a suspended
                    // sender, poisoning the cell and restarting instead.
                    // Otherwise, try to store the specified waiter in the cell.
                    val senders = sendersAndCloseStatus.value.sendersCounter
                    if (r < senders) {
                        // The cell is already covered by sender,
                        // so a rendezvous must happen. Unfortunately,
                        // the cell is empty, so the operation poisons it.
                        if (segment.casState(index, state, POISONED)) {
                            // When the cell becomes poisoned, it is essentially
                            // the same as storing an already cancelled receiver.
                            // Thus, the `expandBuffer()` procedure should be invoked.
                            expandBuffer()
                            return FAILED
                        }
                    } else {
                        // This `receive()` operation should suspend.
                        if (waiter === null) {
                            // The waiter is not specified;
                            // return the corresponding result.
                            return SUSPEND_NO_WAITER
                        }
                        // Try to install the waiter.
                        if (segment.casState(index, state, waiter)) {
                            // The waiter has been successfully installed.
                            // Invoke the `expandBuffer()` procedure and finish.
                            expandBuffer()
                            return SUSPEND
                        }
                    }
                }
                // The cell stores a buffered element.
                state === BUFFERED -> if (segment.casState(index, state, DONE_RCV)) {
                    // Retrieve the element and expand the buffer.
                    expandBuffer()
                    return segment.retrieveElement(index)
                }
                // The cell stores an interrupted sender.
                state === INTERRUPTED_SEND -> return FAILED
                // The cell is already poisoned by a concurrent
                // `hasElements` call. Restart in this case.
                state === POISONED -> return FAILED
                // This channel is already closed.
                state === CHANNEL_CLOSED -> {
                    // Although the channel is closed, it is still required
                    // to call the `expandBuffer()` procedure to keep
                    // `waitForExpandBufferCompletion()` correct.
                    expandBuffer()
                    return FAILED
                }
                // A concurrent `expandBuffer()` is resuming a
                // suspended sender. Wait in a spin-loop until
                // the resumption attempt completes: the cell
                // state must change to either `BUFFERED` or
                // `INTERRUPTED_SEND`.
                state === RESUMING_BY_EB -> continue
                // The cell stores a suspended sender; try to resume it.
                else -> {
                    // To synchronize with expandBuffer(), the algorithm
                    // first moves the cell to an intermediate `S_RESUMING_BY_RCV`
                    // state, updating it to either `BUFFERED` (on success) or
                    // `INTERRUPTED_SEND` (on failure).
                    if (segment.casState(index, state, RESUMING_BY_RCV)) {
                        // Has a concurrent `expandBuffer()` delegated its completion?
                        val helpExpandBuffer = state is WaiterEB
                        // Extract the sender if needed and try to resume it.
                        val sender = if (state is WaiterEB) state.waiter else state
                        return if (sender.tryResumeSender(segment, index)) {
                            // The sender has been resumed successfully!
                            // Update the cell state correspondingly,
                            // expand the buffer, and return the element
                            // stored in the cell.
                            // In case a concurrent `expandBuffer()` has delegated
                            // its completion, the procedure should finish, as the
                            // sender is resumed. Thus, no further action is required.
                            segment.setState(index, DONE_RCV)
                            expandBuffer()
                            segment.retrieveElement(index)
                        } else {
                            // The resumption has failed. Update the cell correspondingly.
                            // In case a concurrent `expandBuffer()` has delegated
                            // its completion, the procedure should skip this cell, so
                            // `expandBuffer()` should be called once again.
                            segment.setState(index, INTERRUPTED_SEND)
                            segment.onCancelledRequest(index, false)
                            if (helpExpandBuffer) expandBuffer()
                            FAILED
                        }
                    }
                }
            }
        }
    }

    private fun Any.tryResumeSender(segment: ChannelSegment<E>, index: Int): Boolean = when (this) {
        is CancellableContinuation<*> -> { // suspended `send(e)` operation
            @Suppress("UNCHECKED_CAST")
            this as CancellableContinuation<Unit>
            tryResume0(Unit)
        }
        is SelectInstance<*> -> {
            this as SelectImplementation<*>
            val trySelectResult = trySelectDetailed(clauseObject = this@BufferedChannel, result = Unit)
            // Clean the element slot to avoid memory leaks
            // if this `select` clause should be re-registered.
            if (trySelectResult === REREGISTER) segment.cleanElement(index)
            // Was the resumption successful?
            trySelectResult === SUCCESSFUL
        }
        is SendBroadcast -> cont.tryResume0(true) // // suspended `sendBroadcast(e)` operation
        else -> error("Unexpected waiter: $this")
    }

    // ################################
    // # The expandBuffer() procedure #
    // ################################

    private fun expandBuffer() {
        // Do not need to take any action if
        // this channel is rendezvous or unlimited.
        if (isRendezvousOrUnlimited) return
        // Read the current segment of
        // the `expandBuffer()` procedure.
        var segment = bufferEndSegment.value
        // Try to expand the buffer until succeed.
        try_again@ while (true) {
            // Increment the logical end of the buffer.
            // The `b`-th cell is going to be added to the buffer.
            val b = bufferEnd.getAndIncrement()
            val id = b / SEGMENT_SIZE
            // After that, read the current `senders` counter.
            // In case its value is lower than `b`, the `send(e)`
            // invocation that will work with this `b`-th cell
            // will detect that the cell is already a part of the
            // buffer when comparing with the `bufferEnd` counter.
            // However, `bufferEndSegment` may reference an outdated
            // segment, which should be updated to avoid memory leaks.
            val s = sendersCounter
            if (s <= b) {
                // Should `bufferEndSegment` be moved forward to avoid memory leaks?
                if (segment.id < id && segment.next != null)
                    moveSegmentBufferEndToSpecifiedOrLast(id, segment)
                // Increment the number of completed `expandBuffer()`-s and finish.
                incCompletedExpandBufferAttempts()
                return
            }
            // Is `bufferEndSegment` outdated?
            // Find the required segment, creating new ones if needed.
            if (segment.id < id) {
                segment = findSegmentBufferEnd(id, segment, b)
                    // Restart if the required segment is removed, or
                    // the linked list of segments is already closed,
                    // and the required one will never be created.
                    // Please note that `findSegmentBuffer(..)` updates
                    // the number of completed `expandBuffer()` attempt
                    // in this case.
                    ?: continue@try_again
            }
            // Try to add the cell to the logical buffer,
            // updating the cell state according to the state-machine.
            val i = (b % SEGMENT_SIZE).toInt()
            if (updateCellExpandBuffer(segment, i, b)) {
                // The cell has been added to the logical buffer!
                // Increment the number of completed `expandBuffer()`-s and finish.
                //
                // Note that it is possible to increment the number of
                // completed `expandBuffer()` attempts earlier, right
                // after the segment is obtained. We find this change
                // counter-intuitive and prefer to avoid it.
                incCompletedExpandBufferAttempts()
                return
            } else {
                // The cell has not been added to the buffer.
                // Increment the number of completed `expandBuffer()`
                // attempts and restart.
                incCompletedExpandBufferAttempts()
                continue@try_again
            }
        }
    }

    private fun updateCellExpandBuffer(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int,
        /* The global index of the cell. */
        b: Long
    ): Boolean {
        // This is a fast-path of `updateCellExpandBufferSlow(..)`.
        //
        // Read the current cell state.
        val state = segment.getState(index)
        if (state is Waiter) {
            // Usually, a sender is stored in the cell.
            // However, it is possible for a concurrent
            // receiver to be already suspended there.
            // Try to distinguish whether the waiter is a
            // sender by comparing the global cell index with
            // the `receivers` counter. In case the cell is not
            // covered by a receiver, a sender is stored in the cell.
            if (b >= receivers.value) {
                // The cell stores a suspended sender. Try to resume it.
                // To synchronize with a concurrent `receive()`, the algorithm
                // first moves the cell state to an intermediate `RESUMING_BY_EB`
                // state, updating it to either `BUFFERED` (on successful resumption)
                // or `INTERRUPTED_SEND` (on failure).
                if (segment.casState(index, state, RESUMING_BY_EB)) {
                    return if (state.tryResumeSender(segment, index)) {
                        // The sender has been resumed successfully!
                        // Move the cell to the logical buffer and finish.
                        segment.setState(index, BUFFERED)
                        true
                    } else {
                        // The resumption has failed.
                        segment.setState(index, INTERRUPTED_SEND)
                        segment.onCancelledRequest(index, false)
                        false
                    }
                }
            }
        }
        return updateCellExpandBufferSlow(segment, index, b)
    }

    private fun updateCellExpandBufferSlow(
        /* The working cell is specified by
        the segment and the index in it. */
        segment: ChannelSegment<E>,
        index: Int,
        /* The global index of the cell. */
        b: Long
    ): Boolean {
        // Update the cell state according to its state machine.
        // See the paper mentioned in the very beginning for
        // the cell life-cycle and the algorithm details.
        while (true) {
            // Read the current cell state.
            val state = segment.getState(index)
            when {
                // A suspended waiter, sender or receiver.
                state is Waiter -> {
                    // Usually, a sender is stored in the cell.
                    // However, it is possible for a concurrent
                    // receiver to be already suspended there.
                    // Try to distinguish whether the waiter is a
                    // sender by comparing the global cell index with
                    // the `receivers` counter. In case the cell is not
                    // covered by a receiver, a sender is stored in the cell.
                    if (b < receivers.value) {
                        // The algorithm cannot distinguish whether the
                        // suspended in the cell operation is sender or receiver.
                        // To make progress, `expandBuffer()` delegates its completion
                        // to an upcoming pairwise request, atomically wrapping
                        // the waiter in `WaiterEB`. In case a sender is stored
                        // in the cell, the upcoming receiver will call `expandBuffer()`
                        // if the sender resumption fails; thus, effectively, skipping
                        // this cell. Otherwise, if a receiver is stored in the cell,
                        // this `expandBuffer()` procedure must finish; therefore,
                        // sender ignore the `WaiterEB` wrapper.
                        if (segment.casState(index, state, WaiterEB(waiter = state)))
                            return true
                    } else {
                        // The cell stores a suspended sender. Try to resume it.
                        // To synchronize with a concurrent `receive()`, the algorithm
                        // first moves the cell state to an intermediate `RESUMING_BY_EB`
                        // state, updating it to either `BUFFERED` (on successful resumption)
                        // or `INTERRUPTED_SEND` (on failure).
                        if (segment.casState(index, state, RESUMING_BY_EB)) {
                            return if (state.tryResumeSender(segment, index)) {
                                // The sender has been resumed successfully!
                                // Move the cell to the logical buffer and finish.
                                segment.setState(index, BUFFERED)
                                true
                            } else {
                                // The resumption has failed.
                                segment.setState(index, INTERRUPTED_SEND)
                                segment.onCancelledRequest(index, false)
                                false
                            }
                        }
                    }
                }
                // The cell stores an interrupted sender, skip it.
                state === INTERRUPTED_SEND -> return false
                // The cell is empty, a concurrent sender is coming.
                state === null -> {
                    // To inform a concurrent sender that this cell is
                    // already a part of the buffer, the algorithm moves
                    // it to a special `IN_BUFFER` state.
                    if (segment.casState(index, state, IN_BUFFER)) return true
                }
                // The cell is already a part of the buffer, finish.
                state === BUFFERED -> return true
                // The cell is already processed by a receiver, no further action is required.
                state === POISONED || state === DONE_RCV || state === INTERRUPTED_RCV -> return true
                // The channel is closed, all the following
                // cells are already in the same state, finish.
                state === CHANNEL_CLOSED -> return true
                // A concurrent receiver is resuming the suspended sender.
                // Wait in a spin-loop until it changes the cell state
                // to either `DONE_RCV` or `INTERRUPTED_SEND`.
                state === RESUMING_BY_RCV -> continue // spin wait
                else -> error("Unexpected cell state: $state")
            }
        }
    }

    /**
     * Increments the counter of completed [expandBuffer] invocations.
     * To guarantee starvation-freedom for [waitExpandBufferCompletion],
     * which waits until the counters of started and completed [expandBuffer] calls
     * coincide and become greater or equal to the specified value,
     * [waitExpandBufferCompletion] may set a flag that pauses further progress.
     */
    private fun incCompletedExpandBufferAttempts(nAttempts: Long = 1) {
        // Increment the number of completed `expandBuffer()` calls.
        completedExpandBuffersAndPauseFlag.addAndGet(nAttempts).also {
            // Should further `expandBuffer()`-s be paused?
            // If so, this thread should wait in a spin-loop
            // until the flag is unset.
            if (it.ebPauseExpandBuffers) {
                @Suppress("ControlFlowWithEmptyBody")
                while (completedExpandBuffersAndPauseFlag.value.ebPauseExpandBuffers) {}
            }
        }
    }

    /**
     * Waits in a spin-loop until the [expandBuffer] call that
     * should process the [globalIndex]-th cell is completed.
     * Essentially, it waits until the numbers of started ([bufferEnd])
     * and completed ([completedExpandBuffersAndPauseFlag]) [expandBuffer]
     * attempts coincide and become equal or greater than [globalIndex].
     * To avoid starvation, this function may set a flag
     * that pauses further progress.
     */
    internal fun waitExpandBufferCompletion(globalIndex: Long) {
        // Do nothing if this channel is rendezvous or unlimited;
        // `expandBuffer()` is not used in these cases.
        if (isRendezvousOrUnlimited) return
        // Wait in an infinite loop until the number of started
        // buffer expansion calls become not lower than the cell index.
        @Suppress("ControlFlowWithEmptyBody")
        while (bufferEndCounter <= globalIndex) {}
        // Now it is guaranteed that the `expandBuffer()` call that
        // should process the required cell has been started.
        // Wait in a fixed-size spin-loop until the numbers of
        // started and completed buffer expansion calls coincide.
        repeat(EXPAND_BUFFER_COMPLETION_WAIT_ITERATIONS) {
            // Read the number of started buffer expansion calls.
            val b = bufferEndCounter
            // Read the number of completed buffer expansion calls.
            val ebCompleted = completedExpandBuffersAndPauseFlag.value.ebCompletedCounter
            // Do the numbers of started and completed calls coincide?
            // Note that we need to re-read the number of started `expandBuffer()`
            // calls to obtain a correct snapshot.
            // Here we wait to a precise match in order to ensure that **our matching expandBuffer()**
            // completed. The only way to ensure that is to check that number of started expands == number of finished expands
            if (b == ebCompleted && b == bufferEndCounter) return
        }
        // To avoid starvation, pause further `expandBuffer()` calls.
        completedExpandBuffersAndPauseFlag.update {
            constructEBCompletedAndPauseFlag(it.ebCompletedCounter, true)
        }
        // Now wait in an infinite spin-loop until the counters coincide.
        while (true) {
            // Read the number of started buffer expansion calls.
            val b = bufferEndCounter
            // Read the number of completed buffer expansion calls
            // along with the flag that pauses further progress.
            val ebCompletedAndBit = completedExpandBuffersAndPauseFlag.value
            val ebCompleted = ebCompletedAndBit.ebCompletedCounter
            val pauseExpandBuffers = ebCompletedAndBit.ebPauseExpandBuffers
            // Do the numbers of started and completed calls coincide?
            // Note that we need to re-read the number of started `expandBuffer()`
            // calls to obtain a correct snapshot.
            if (b == ebCompleted && b == bufferEndCounter) {
                // Unset the flag, which pauses progress, and finish.
                completedExpandBuffersAndPauseFlag.update {
                    constructEBCompletedAndPauseFlag(it.ebCompletedCounter, false)
                }
                return
            }
            // It is possible that a concurrent caller of this function
            // has unset the flag, which pauses further progress to avoid
            // starvation. In this case, set the flag back.
            if (!pauseExpandBuffers) {
                completedExpandBuffersAndPauseFlag.compareAndSet(
                    ebCompletedAndBit,
                    constructEBCompletedAndPauseFlag(ebCompleted, true)
                )
            }
        }
    }


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
    protected open fun registerSelectForSend(select: SelectInstance<*>, element: Any?) =
        sendImpl( // <-- this is an inline function
            element = element as E,
            waiter = select,
            onRendezvousOrBuffered = { select.selectInRegistrationPhase(Unit) },
            onSuspend = { _, _ -> },
            onClosed = { onClosedSelectOnSend(element, select) }
        )


    private fun onClosedSelectOnSend(element: E, select: SelectInstance<*>) {
        onUndeliveredElement?.callUndeliveredElement(element, select.context)
        select.selectInRegistrationPhase(CHANNEL_CLOSED)
    }

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

    @Suppress("UNUSED_PARAMETER")
    private fun registerSelectForReceive(select: SelectInstance<*>, ignoredParam: Any?) =
        receiveImpl( // <-- this is an inline function
            waiter = select,
            onElementRetrieved = { elem -> select.selectInRegistrationPhase(elem) },
            onSuspend = { _, _, _ -> },
            onClosed = { onClosedSelectOnReceive(select) }
        )

    private fun onClosedSelectOnReceive(select: SelectInstance<*>) {
        select.selectInRegistrationPhase(CHANNEL_CLOSED)
    }

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
    private inner class BufferedChannelIterator : ChannelIterator<E>, BeforeResumeCancelHandler(), Waiter {
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
        private var segment: Segment<*>? = null
        private var index = -1

        /**
         * Invoked on cancellation, [BeforeResumeCancelHandler] implementation.
         */
        override fun invoke(cause: Throwable?) {
            segment?.onCancellation(index, null)
        }

        // `hasNext()` is just a special receive operation.
        override suspend fun hasNext(): Boolean =
            receiveImpl( // <-- this is an inline function
                // Do not create a continuation until it is required;
                // it is created later via [onNoWaiterSuspend], if needed.
                waiter = null,
                // Store the received element in `receiveResult` on successful
                // retrieval from the buffer or rendezvous with a suspended sender.
                // Also, inform the `BufferedChannel` extensions that
                // the synchronization of this receive operation is completed.
                onElementRetrieved = { element ->
                    this.receiveResult = element
                    true
                },
                // As no waiter is provided, suspension is impossible.
                onSuspend = { _, _, _ -> error("unreachable") },
                // Return `false` or throw an exception if the channel is already closed.
                onClosed = { onClosedHasNext() },
                // If `hasNext()` decides to suspend, the corresponding
                // `suspend` function that creates a continuation is called.
                // The tail-call optimization is applied here.
                onNoWaiterSuspend = { segm, i, r -> return hasNextOnNoWaiterSuspend(segm, i, r) }
            )

        private fun onClosedHasNext(): Boolean {
            this.receiveResult = CHANNEL_CLOSED
            val cause = closeCause ?: return false
            throw recoverStackTrace(cause)
        }

        private suspend fun hasNextOnNoWaiterSuspend(
            /* The working cell is specified by
            the segment and the index in it. */
            segment: ChannelSegment<E>,
            index: Int,
            /* The global index of the cell. */
            r: Long
        ): Boolean = suspendCancellableCoroutineReusable { cont ->
            this.continuation = cont
            receiveImplOnNoWaiter( // <-- this is an inline function
                segment = segment, index = index, r = r,
                waiter = this, // store this iterator as a waiter
                // In case of successful element retrieval, store
                // it in `receiveResult` and resume the continuation.
                // Importantly, the receiver coroutine may be cancelled
                // after it is successfully resumed but not dispatched yet.
                // In case `onUndeliveredElement` is present, we must
                // invoke it in the latter case.
                onElementRetrieved = { element ->
                    this.receiveResult = element
                    this.continuation = null
                    cont.resume(true, onUndeliveredElement?.bindCancellationFun(element, cont.context))
                },
                onClosed = { onClosedHasNextNoWaiterSuspend() }
            )
        }

        override fun invokeOnCancellation(segment: Segment<*>, index: Int) {
            this.segment = segment
            this.index = index
            // It is possible that this `hasNext()` invocation is already
            // resumed, and the `continuation` field is already updated to `null`.
            this.continuation?.invokeOnCancellation(this.asHandler)
        }

        private fun onClosedHasNextNoWaiterSuspend() {
            // Read the current continuation and clean
            // the corresponding field to avoid memory leaks.
            val cont = this.continuation!!
            this.continuation = null
            // Update the `hasNext()` internal result.
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

        fun tryResumeHasNext(element: E): Boolean {
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
        sendersAndCloseStatus.update { cur ->
            when (cur.sendersCloseStatus) {
                CLOSE_STATUS_ACTIVE -> // the channel is neither closed nor cancelled
                    constructSendersAndCloseStatus(cur.sendersCounter, CLOSE_STATUS_CLOSED)
                CLOSE_STATUS_CANCELLATION_STARTED -> // the channel is going to be cancelled
                    constructSendersAndCloseStatus(cur.sendersCounter, CLOSE_STATUS_CANCELLED)
                else -> return // the channel is already marked as closed or cancelled.
            }
        }

    /**
     * Marks this channel as cancelled.
     *
     * All operation that notice this channel in the cancelled state,
     * must help to complete the cancellation via [completeCloseOrCancel].
     */
    private fun markCancelled(): Unit =
        sendersAndCloseStatus.update { cur ->
            constructSendersAndCloseStatus(cur.sendersCounter, CLOSE_STATUS_CANCELLED)
        }

    /**
     * When the cancellation procedure starts, it is critical
     * to mark the closing status correspondingly. Thus, other
     * operations, which may help to complete the cancellation,
     * always correctly update the status to `CANCELLED`.
     */
    private fun markCancellationStarted(): Unit =
        sendersAndCloseStatus.update { cur ->
            if (cur.sendersCloseStatus == CLOSE_STATUS_ACTIVE)
                constructSendersAndCloseStatus(cur.sendersCounter, CLOSE_STATUS_CANCELLATION_STARTED)
            else return // this channel is already closed or cancelled
        }

    /**
     * Completes the started [close] or [cancel] procedure.
     */
    private fun completeCloseOrCancel() {
        isClosedForSend // must finish the started close/cancel if one is detected.
    }

    protected open val isConflatedDropOldest get() = false

    /**
     * Completes the channel closing procedure.
     */
    private fun completeClose(sendersCur: Long): ChannelSegment<E> {
        // Close the linked list for further segment addition,
        // obtaining the last segment in the data structure.
        val lastSegment = closeLinkedList()
        // In the conflated channel implementation (with the DROP_OLDEST
        // elements conflation strategy), it is critical to mark all empty
        // cells as closed to prevent in-progress `send(e)`-s, which have not
        // put their elements yet, completions after this channel is closed.
        // Otherwise, it is possible for a `send(e)` to put an element when
        // the buffer is already full, while a concurrent receiver may extract
        // the oldest element. When the channel is not closed, we can linearize
        // this `receive()` before the `send(e)`, but after the channel is closed,
        // `send(e)` must fails. Marking all unprocessed cells as `CLOSED` solves the issue.
        if (isConflatedDropOldest) {
            val lastBufferedCellGlobalIndex = markAllEmptyCellsAsClosed(lastSegment)
            if (lastBufferedCellGlobalIndex != -1L)
                dropFirstElementUntilTheSpecifiedCellIsInTheBuffer(lastBufferedCellGlobalIndex)
        }
        // Resume waiting `receive()` requests,
        // informing them that the channel is closed.
        cancelSuspendedReceiveRequests(lastSegment, sendersCur)
        // Return the last segment in the linked list as a result
        // of this function; we need it in `completeCancel(..)`.
        return lastSegment
    }

    /**
     * Completes the channel cancellation procedure.
     */
    private fun completeCancel(sendersCur: Long) {
        // First, ensure that this channel is closed,
        // obtaining the last segment in the linked list.
        val lastSegment = completeClose(sendersCur)
        // Cancel suspended `send(e)` requests and
        // remove buffered elements in the reverse order.
        removeUnprocessedElements(lastSegment)
    }

    /**
     * Closes the underlying linked list of segments for further segment addition.
     */
    private fun closeLinkedList(): ChannelSegment<E> {
        // Choose the last segment.
        var lastSegment = bufferEndSegment.value
        sendSegment.value.let { if (it.id > lastSegment.id) lastSegment = it }
        receiveSegment.value.let { if (it.id > lastSegment.id) lastSegment = it }
        // Close the linked list of segment for new segment addition
        // and return the last segment in the linked list.
        return lastSegment.close()
    }

    /**
     * This function marks all empty cells, in the `null` and [IN_BUFFER] state,
     * as closed. Notably, it processes the cells from right to left, and finishes
     * immediately when the processing cell is already covered by `receive()` or
     * contains a buffered elements ([BUFFERED] state).
     *
     * This function returns the global index of the last buffered element,
     * or `-1` if this channel does not contain buffered elements.
     */
    private fun markAllEmptyCellsAsClosed(lastSegment: ChannelSegment<E>): Long {
        // Process the cells in reverse order, from right to left.
        var segment = lastSegment
        while (true) {
            for (index in SEGMENT_SIZE - 1 downTo 0) {
                // Is this cell already covered by `receive()`?
                val globalIndex = segment.id * SEGMENT_SIZE + index
                if (globalIndex < receiversCounter) return -1
                // Process the cell `segment[index]`.
                cell_update@ while (true) {
                    val state = segment.getState(index)
                    when {
                        // The cell is empty.
                        state === null || state === IN_BUFFER -> {
                            // Inform a possibly upcoming sender that this channel is already closed.
                            if (segment.casState(index, state, CHANNEL_CLOSED)) {
                                segment.onSlotCleaned()
                                break@cell_update
                            }
                        }
                        // The cell stores a buffered element.
                        state === BUFFERED -> return globalIndex
                        // Skip this cell if it is not empty and does not store a buffered element.
                        else -> break@cell_update
                    }
                }
            }
            // Process the next segment, finishing if the linked list ends.
            segment = segment.prev ?: return -1
        }
    }

    /**
     * Cancels suspended `send(e)` requests and removes buffered elements
     * starting from the last cell in the specified [lastSegment] (it must
     * be the physical tail of the underlying linked list) and updating
     * the cells in reverse order.
     */
    private fun removeUnprocessedElements(lastSegment: ChannelSegment<E>) {
        // Read the `onUndeliveredElement` lambda at once. In case it
        // throws an exception, this exception is handled and stored in
        // the variable below. If multiple exceptions are thrown, the first
        // one is stored in the variable, while the others are suppressed.
        val onUndeliveredElement = onUndeliveredElement
        var undeliveredElementException: UndeliveredElementException? = null // first cancel exception, others suppressed
        // To perform synchronization correctly, it is critical to
        // process the cells in reverse order, from right to left.
        // However, according to the API, suspended senders should
        // be cancelled in the order of their suspension. Therefore,
        // we need to collect all of them and cancel in the reverse
        // order after that.
        var suspendedSenders = InlineList<Waiter>()
        var segment = lastSegment
        process_segments@ while (true) {
            for (index in SEGMENT_SIZE - 1 downTo 0) {
                // Process the cell `segment[index]`.
                val globalIndex = segment.id * SEGMENT_SIZE + index
                // Update the cell state.
                update_cell@ while (true) {
                    // Read the current state of the cell.
                    val state = segment.getState(index)
                    when {
                        // The cell is already processed by a receiver.
                        state === DONE_RCV -> break@process_segments
                        // The cell stores a buffered element.
                        state === BUFFERED -> {
                            // Is the cell already covered by a receiver?
                            if (globalIndex < receiversCounter) break@process_segments
                            // Update the cell state to `CHANNEL_CLOSED`.
                            if (segment.casState(index, state, CHANNEL_CLOSED)) {
                                // If `onUndeliveredElement` lambda is non-null, call it.
                                if (onUndeliveredElement != null) {
                                    val element = segment.getElement(index)
                                    undeliveredElementException = onUndeliveredElement.callUndeliveredElementCatchingException(element, undeliveredElementException)
                                }
                                // Clean the element field and inform the segment
                                // that the slot is cleaned to avoid memory leaks.
                                segment.cleanElement(index)
                                segment.onSlotCleaned()
                                break@update_cell
                            }
                        }
                        // The cell is empty.
                        state === IN_BUFFER || state === null -> {
                            // Update the cell state to `CHANNEL_CLOSED`.
                            if (segment.casState(index, state, CHANNEL_CLOSED)) {
                                // Inform the segment that the slot is cleaned to avoid memory leaks.
                                segment.onSlotCleaned()
                                break@update_cell
                            }
                        }
                        // The cell stores a suspended waiter.
                        state is Waiter || state is WaiterEB -> {
                            // Is the cell already covered by a receiver?
                            if (globalIndex < receiversCounter) break@process_segments
                            // Obtain the sender.
                            val sender: Waiter = if (state is WaiterEB) state.waiter
                                                 else state as Waiter
                            // Update the cell state to `CHANNEL_CLOSED`.
                            if (segment.casState(index, state, CHANNEL_CLOSED)) {
                                // If `onUndeliveredElement` lambda is non-null, call it.
                                if (onUndeliveredElement != null) {
                                    val element = segment.getElement(index)
                                    undeliveredElementException = onUndeliveredElement.callUndeliveredElementCatchingException(element, undeliveredElementException)
                                }
                                // Save the sender for further cancellation.
                                suspendedSenders += sender
                                // Clean the element field and inform the segment
                                // that the slot is cleaned to avoid memory leaks.
                                segment.cleanElement(index)
                                segment.onSlotCleaned()
                                break@update_cell
                            }
                        }
                        // A concurrent receiver is resuming a suspended sender.
                        // As the cell is covered by a receiver, finish immediately.
                        state === RESUMING_BY_EB || state === RESUMING_BY_RCV -> break@process_segments
                        // A concurrent `expandBuffer()` is resuming a suspended sender.
                        // Wait in a spin-loop until the cell state changes.
                        state === RESUMING_BY_EB -> continue@update_cell
                        else -> break@update_cell
                    }
                }
            }
            // Process the previous segment.
            segment = segment.prev ?: break
        }
        // Cancel suspended senders in their order of addition to this channel.
        suspendedSenders.forEachReversed { it.resumeSenderOnCancelledChannel() }
        // Throw `UndeliveredElementException` at the end if there was one.
        undeliveredElementException?.let { throw it }
    }

    /**
     * Cancels suspended `receive` requests from the end to the beginning,
     * also moving empty cells to the `CHANNEL_CLOSED` state.
     */
    private fun cancelSuspendedReceiveRequests(lastSegment: ChannelSegment<E>, sendersCounter: Long) {
        // To perform synchronization correctly, it is critical to
        // extract suspended requests in the reverse order,
        // from the end to the beginning.
        // However, according to the API, they should be cancelled
        // in the order of their suspension. Therefore, we need to
        // collect the suspended requests first, cancelling them
        // in the reverse order after that.
        var suspendedReceivers = InlineList<Waiter>()
        var segment: ChannelSegment<E>? = lastSegment
        process_segments@ while (segment != null) {
            for (index in SEGMENT_SIZE - 1 downTo 0) {
                // Is the cell already covered by a sender? Finish immediately in this case.
                if (segment.id * SEGMENT_SIZE + index < sendersCounter) break@process_segments
                // Try to move the cell state to `CHANNEL_CLOSED`.
                cell_update@ while (true) {
                    val state = segment.getState(index)
                    when {
                        state === null || state === IN_BUFFER -> {
                            if (segment.casState(index, state, CHANNEL_CLOSED)) {
                                segment.onSlotCleaned()
                                break@cell_update
                            }
                        }
                        state is WaiterEB -> {
                            if (segment.casState(index, state, CHANNEL_CLOSED)) {
                                suspendedReceivers += state.waiter // save for cancellation.
                                segment.onCancelledRequest(index = index, receiver = true)
                                break@cell_update
                            }
                        }
                        state is Waiter -> {
                            if (segment.casState(index, state, CHANNEL_CLOSED)) {
                                suspendedReceivers += state // save for cancellation.
                                segment.onCancelledRequest(index = index, receiver = true)
                                break@cell_update
                            }
                        }
                        else -> break@cell_update // nothing to cancel.
                    }
                }
            }
            // Process the previous segment.
            segment = segment.prev
        }
        // Cancel the suspended requests in their order of addition to this channel.
        suspendedReceivers.forEachReversed { it.resumeReceiverOnClosedChannel() }
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
            is SendBroadcast -> cont.resume(false)
            is CancellableContinuation<*> -> resumeWithException(if (receiver) receiveException else sendException)
            is ReceiveCatching<*> -> cont.resume(closed(closeCause))
            is BufferedChannel<*>.BufferedChannelIterator -> tryResumeHasNextOnClosedChannel()
            is SelectInstance<*> -> trySelect(this@BufferedChannel, CHANNEL_CLOSED)
            else -> error("Unexpected waiter: $this")
        }
    }

    @ExperimentalCoroutinesApi
    override val isClosedForSend: Boolean
        get() = sendersAndCloseStatus.value.isClosedForSend0

    private val Long.isClosedForSend0 get() =
        isClosed(this, isClosedForReceive = false)

    @ExperimentalCoroutinesApi
    override val isClosedForReceive: Boolean
        get() = sendersAndCloseStatus.value.isClosedForReceive0

    private val Long.isClosedForReceive0 get() =
        isClosed(this, isClosedForReceive = true)

    private fun isClosed(
        sendersAndCloseStatusCur: Long,
        isClosedForReceive: Boolean
    ) = when (sendersAndCloseStatusCur.sendersCloseStatus) {
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
            completeClose(sendersAndCloseStatusCur.sendersCounter)
            // When `isClosedForReceive` is `false`, always return `true`.
            // Otherwise, it is possible that the channel is closed but
            // still has elements to retrieve.
            if (isClosedForReceive) !hasElements() else true
        }
        // This channel has been successfully cancelled.
        // Help to complete the cancellation procedure to
        // guarantee linearizability and return `true`.
        CLOSE_STATUS_CANCELLED -> {
            completeCancel(sendersAndCloseStatusCur.sendersCounter)
            true
        }
        else -> error("unexpected close status: ${sendersAndCloseStatusCur.sendersCloseStatus}")
    }

    @ExperimentalCoroutinesApi
    override val isEmpty: Boolean get() {
        // This function should return `false` if
        // this channel is closed for `receive`.
        if (isClosedForReceive) return false
        // Does this channel has elements to retrieve?
        if (hasElements()) return false
        // This channel does not have elements to retrieve;
        // Check that it is still not closed for `receive`.
        return !isClosedForReceive
    }

    /**
     * Checks whether this channel contains elements to retrieve.
     * Unfortunately, simply comparing the counters is insufficient,
     * as some cells can be in the `INTERRUPTED` state due to cancellation.
     * This function tries to find the first "alive" element,
     * updating the `receivers` counter to skip empty cells.
     *
     * The implementation is similar to `receive()`.
     */
    internal fun hasElements(): Boolean {
        while (true) {
            // Read the segment before obtaining the `receivers` counter value.
            var segment = receiveSegment.value
            // Obtains the `receivers` and `senders` counter values.
            val r = receiversCounter
            val s = sendersCounter
            // Is there a chance that this channel has elements?
            if (s <= r) return false // no elements
            // The `r`-th cell is covered by a sender; check whether it contains an element.
            // First, try to find the required segment if the initially
            // obtained segment (in the beginning of this function) has lower id.
            val id = r / SEGMENT_SIZE
            if (segment.id != id) {
                // Try to find the required segment.
                segment = findSegmentReceive(id, segment) ?:
                    // The required segment has not been found. Either it has already
                    // been removed, or the underlying linked list is already closed
                    // for segment additions. In the latter case, the channel is closed
                    // and does not contain elements, so this operation returns `false`.
                    // Otherwise, if the required segment is removed, the operation restarts.
                    if (receiveSegment.value.id < id) return false else continue
            }
            segment.cleanPrev() // all the previous segments are no longer needed.
            // Does the `r`-th cell contain waiting sender or buffered element?
            val i = (r % SEGMENT_SIZE).toInt()
            if (isCellNonEmpty(segment, i, r)) return true
            // The cell is empty. Update `receivers` counter and try again.
            receivers.compareAndSet(r, r + 1) // if this CAS fails, the counter has already been updated.
        }
    }

    /**
     * Checks whether this cell contains a buffered element or a waiting sender,
     * returning `true` in this case. Otherwise, if this cell is empty
     * (due to waiter cancellation, cell poisoning, or channel closing),
     * this function returns `false`.
     *
     * Notably, this function must be called only if the cell is covered by a sender.
     */
    private fun isCellNonEmpty(
        segment: ChannelSegment<E>,
        index: Int,
        globalIndex: Long
    ): Boolean {
        // The logic is similar to `updateCellReceive` with the only difference
        // that this function neither changes the cell state nor retrieves the element.
        while (true) {
            // Read the current cell state.
            val state = segment.getState(index)
            when {
                // The cell is empty but a sender is coming.
                state === null || state === IN_BUFFER -> {
                    // Poison the cell to ensure correctness.
                    if (segment.casState(index, state, POISONED)) {
                        // When the cell becomes poisoned, it is essentially
                        // the same as storing an already cancelled receiver.
                        // Thus, the `expandBuffer()` procedure should be invoked.
                        expandBuffer()
                        return false
                    }
                }
                // The cell stores a buffered element.
                state === BUFFERED -> return true
                // The cell stores an interrupted sender.
                state === INTERRUPTED_SEND -> return false
                // This channel is already closed.
                state === CHANNEL_CLOSED -> return false
                // The cell is already processed
                // by a concurrent receiver.
                state === DONE_RCV -> return false
                // The cell is already poisoned
                // by a concurrent receiver.
                state === POISONED -> return false
                // A concurrent `expandBuffer()` is resuming
                // a suspended sender. This function is eligible
                // to linearize before the buffer expansion procedure.
                state === RESUMING_BY_EB -> return true
                // A concurrent receiver is resuming
                // a suspended sender. The element
                // is no longer available for retrieval.
                state === RESUMING_BY_RCV -> return false
                // The cell stores a suspended request.
                // However, it is possible that this request
                // is receiver if the cell is covered by both
                // send and receive operations.
                // In case the cell is already covered by
                // a receiver, the element is no longer
                // available for retrieval, and this function
                // return `false`. Otherwise, it is guaranteed
                // that the suspended request is sender, so
                // this function returns `true`.
                else -> return globalIndex == receiversCounter
            }
        }
    }

    // #######################
    // # Segments Management #
    // #######################

    /**
     * Finds the segment with the specified [id] starting by the [startFrom]
     * segment and following the [ChannelSegment.next] references. In case
     * the required segment has not been created yet, this function attempts
     * to add it to the underlying linked list. Finally, it updates [sendSegment]
     * to the found segment if its [ChannelSegment.id] is greater than the one
     * of the already stored segment.
     *
     * In case the requested segment is already removed, or if it should be allocated
     * but the linked list structure is closed for new segments addition, this function
     * returns `null`. The implementation also efficiently skips a sequence of removed
     * segments, updating the counter value in [sendersAndCloseStatus] correspondingly.
     */
    private fun findSegmentSend(id: Long, startFrom: ChannelSegment<E>): ChannelSegment<E>? {
        return sendSegment.findSegmentAndMoveForward(id, startFrom, createSegmentFunction()).let {
            if (it.isClosed) {
                // The required segment has not been found and new segments
                // cannot be added, as the linked listed in already added.
                // This channel is already closed or cancelled; help to complete
                // the closing or cancellation procedure.
                completeCloseOrCancel()
                // Clean the `prev` reference of the provided segment
                // if all the previous cells are already covered by senders.
                // It is important to clean the `prev` reference only in
                // this case, as the closing/cancellation procedure may
                // need correct value to traverse the linked list from right to left.
                if (startFrom.id * SEGMENT_SIZE <  receiversCounter) startFrom.cleanPrev()
                // As the required segment is not found and cannot be allocated, return `null`.
                null
            } else {
                // Get the found segment.
                val segment = it.segment
                // Is the required segment removed?
                if (segment.id > id) {
                    // The required segment has been removed; `segment` is the first
                    // segment with `id` not lower than the required one.
                    // Skip the sequence of removed cells in O(1).
                    updateSendersCounterIfLower(segment.id * SEGMENT_SIZE)
                    // Clean the `prev` reference of the provided segment
                    // if all the previous cells are already covered by senders.
                    // It is important to clean the `prev` reference only in
                    // this case, as the closing/cancellation procedure may
                    // need correct value to traverse the linked list from right to left.
                    if (segment.id * SEGMENT_SIZE <  receiversCounter) segment.cleanPrev()
                    // As the required segment is not found and cannot be allocated, return `null`.
                    null
                } else {
                    assert { segment.id == id }
                    // The required segment has been found; return it!
                    segment
                }
            }
        }
    }

    /**
     * Finds the segment with the specified [id] starting by the [startFrom]
     * segment and following the [ChannelSegment.next] references. In case
     * the required segment has not been created yet, this function attempts
     * to add it to the underlying linked list. Finally, it updates [receiveSegment]
     * to the found segment if its [ChannelSegment.id] is greater than the one
     * of the already stored segment.
     *
     * In case the requested segment is already removed, or if it should be allocated
     * but the linked list structure is closed for new segments addition, this function
     * returns `null`. The implementation also efficiently skips a sequence of removed
     * segments, updating the [receivers] counter correspondingly.
     */
    private fun findSegmentReceive(id: Long, startFrom: ChannelSegment<E>): ChannelSegment<E>? =
        receiveSegment.findSegmentAndMoveForward(id, startFrom, createSegmentFunction()).let {
            if (it.isClosed) {
                // The required segment has not been found and new segments
                // cannot be added, as the linked listed in already added.
                // This channel is already closed or cancelled; help to complete
                // the closing or cancellation procedure.
                completeCloseOrCancel()
                // Clean the `prev` reference of the provided segment
                // if all the previous cells are already covered by senders.
                // It is important to clean the `prev` reference only in
                // this case, as the closing/cancellation procedure may
                // need correct value to traverse the linked list from right to left.
                if (startFrom.id * SEGMENT_SIZE < sendersCounter) startFrom.cleanPrev()
                // As the required segment is not found and cannot be allocated, return `null`.
                null
            } else {
                // Get the found segment.
                val segment = it.segment
                // Advance the `bufferEnd` segment if required.
                if (!isRendezvousOrUnlimited && id <= bufferEndCounter / SEGMENT_SIZE) {
                    bufferEndSegment.moveForward(segment)
                }
                // Is the required segment removed?
                if (segment.id > id) {
                    // The required segment has been removed; `segment` is the first
                    // segment with `id` not lower than the required one.
                    // Skip the sequence of removed cells in O(1).
                    updateReceiversCounterIfLower(segment.id * SEGMENT_SIZE)
                    // Clean the `prev` reference of the provided segment
                    // if all the previous cells are already covered by senders.
                    // It is important to clean the `prev` reference only in
                    // this case, as the closing/cancellation procedure may
                    // need correct value to traverse the linked list from right to left.
                    if (segment.id * SEGMENT_SIZE < sendersCounter) segment.cleanPrev()
                    // As the required segment is already removed, return `null`.
                    null
                } else {
                    assert { segment.id == id }
                    // The required segment has been found; return it!
                    segment
                }
            }
        }

    /**
     * Importantly, when this function does not find the requested segment,
     * it always updates the number of completed `expandBuffer()` attempts.
     */
    private fun findSegmentBufferEnd(id: Long, startFrom: ChannelSegment<E>, currentBufferEndCounter: Long): ChannelSegment<E>? =
        bufferEndSegment.findSegmentAndMoveForward(id, startFrom, createSegmentFunction()).let {
            if (it.isClosed) {
                // The required segment has not been found and new segments
                // cannot be added, as the linked listed in already added.
                // This channel is already closed or cancelled; help to complete
                // the closing or cancellation procedure.
                completeCloseOrCancel()
                // Update `bufferEndSegment` to the last segment
                // in the linked list to avoid memory leaks.
                moveSegmentBufferEndToSpecifiedOrLast(id, startFrom)
                // When this function does not find the requested segment,
                // it should update the number of completed `expandBuffer()` attempts.
                incCompletedExpandBufferAttempts()
                null
            } else {
                // Get the found segment.
                val segment = it.segment
                // Is the required segment removed?
                if (segment.id > id) {
                    // The required segment has been removed; `segment` is the first segment
                    // with `id` not lower than the required one.
                    // Try to skip the sequence of removed cells in O(1) by increasing the `bufferEnd` counter.
                    // Importantly, when this function does not find the requested segment,
                    // it should update the number of completed `expandBuffer()` attempts.
                    if (bufferEnd.compareAndSet(currentBufferEndCounter + 1, segment.id * SEGMENT_SIZE)) {
                        incCompletedExpandBufferAttempts(segment.id * SEGMENT_SIZE - currentBufferEndCounter)
                    } else {
                        incCompletedExpandBufferAttempts()
                    }
                    // As the required segment is already removed, return `null`.
                    null
                } else {
                    assert { segment.id == id }
                    // The required segment has been found; return it!
                    segment
                }
            }
        }

    /**
     * Updates [bufferEndSegment] to the one with the specified [id] or
     * to the last existing segment, if the required segment is not yet created.
     *
     * Unlike [findSegmentBufferEnd], this function does not allocate new segments.
     */
    private fun moveSegmentBufferEndToSpecifiedOrLast(id: Long, startFrom: ChannelSegment<E>) {
        // Start searching the required segment from the specified one.
        var segment: ChannelSegment<E> = startFrom
        while (segment.id < id) {
            segment = segment.next ?: break
        }
        // Skip all removed segments and try to update `bufferEndSegment`
        // to the first non-removed one. This part should succeed eventually,
        // as the tail segment is never removed.
        while (true) {
            while (segment.isRemoved) {
                segment = segment.next ?: break
            }
            // Try to update `bufferEndSegment`. On failure,
            // the found segment is already removed, so it
            // should be skipped.
            if (bufferEndSegment.moveForward(segment)) return
        }
    }

    /**
     * Updates the `senders` counter if its value
     * is lower that the specified one.
     *
     * Senders use this function to efficiently skip
     * a sequence of cancelled receivers.
     */
    private fun updateSendersCounterIfLower(value: Long): Unit =
        sendersAndCloseStatus.loop { cur ->
            val curCounter = cur.sendersCounter
            if (curCounter >= value) return
            val update = constructSendersAndCloseStatus(curCounter, cur.sendersCloseStatus)
            if (sendersAndCloseStatus.compareAndSet(cur, update)) return
        }

    /**
     * Updates the `receivers` counter if its value
     * is lower that the specified one.
     *
     * Receivers use this function to efficiently skip
     * a sequence of cancelled senders.
     */
    private fun updateReceiversCounterIfLower(value: Long): Unit =
        receivers.loop { cur ->
            if (cur >= value) return
            if (receivers.compareAndSet(cur, value)) return
        }

    // ###################
    // # Debug Functions #
    // ###################

    @Suppress("ConvertTwoComparisonsToRangeCheck")
    override fun toString(): String {
        val sb = StringBuilder()
        // Append the close status
        when (sendersAndCloseStatus.value.sendersCloseStatus) {
            CLOSE_STATUS_CLOSED -> sb.append("closed,")
            CLOSE_STATUS_CANCELLED -> sb.append("cancelled,")
        }
        // Append the buffer capacity
        sb.append("capacity=$capacity,")
        // Append the data
        sb.append("data=[")
        val firstSegment = listOf(receiveSegment.value, sendSegment.value, bufferEndSegment.value)
            .filter { it !== NULL_SEGMENT }
            .minBy { it.id }
        val r = receiversCounter
        val s = sendersCounter
        var segment = firstSegment
        append_elements@ while (true) {
            process_cell@ for (i in 0 until SEGMENT_SIZE) {
                val globalCellIndex = segment.id * SEGMENT_SIZE + i
                if (globalCellIndex >= s && globalCellIndex >= r) break@append_elements
                val cellState = segment.getState(i)
                val element = segment.getElement(i)
                val cellStateString = when (cellState) {
                    is CancellableContinuation<*> -> {
                        when {
                            globalCellIndex < r && globalCellIndex >= s -> "receive"
                            globalCellIndex < s && globalCellIndex >= r -> "send"
                            else -> "cont"
                        }
                    }
                    is SelectInstance<*> -> {
                        when {
                            globalCellIndex < r && globalCellIndex >= s -> "onReceive"
                            globalCellIndex < s && globalCellIndex >= r -> "onSend"
                            else -> "select"
                        }
                    }
                    is ReceiveCatching<*> -> "receiveCatching"
                    is SendBroadcast -> "sendBroadcast"
                    is WaiterEB -> "EB($cellState)"
                    RESUMING_BY_RCV, RESUMING_BY_EB -> "resuming_sender"
                    null, IN_BUFFER, DONE_RCV, POISONED, INTERRUPTED_RCV, INTERRUPTED_SEND, CHANNEL_CLOSED -> continue@process_cell
                    else -> cellState.toString() // leave it just in case something is missed.
                }
                if (element != null) {
                    sb.append("($cellStateString,$element),")
                } else {
                    sb.append("$cellStateString,")
                }
            }
            // Process the next segment if exists.
            segment = segment.next ?: break
        }
        if (sb.last() == ',') sb.deleteAt(sb.length - 1)
        sb.append("]")
        // The string representation is constructed.
        return sb.toString()
    }

    // Returns a debug representation of this channel,
    // which is actively used in Lincheck tests.
    internal fun toStringDebug(): String {
        val sb = StringBuilder()
        // Append the counter values and the close status
        sb.append("S=${sendersCounter},R=${receiversCounter},B=${bufferEndCounter},B'=${completedExpandBuffersAndPauseFlag.value},C=${sendersAndCloseStatus.value.sendersCloseStatus},")
        when (sendersAndCloseStatus.value.sendersCloseStatus) {
            CLOSE_STATUS_CANCELLATION_STARTED -> sb.append("CANCELLATION_STARTED,")
            CLOSE_STATUS_CLOSED -> sb.append("CLOSED,")
            CLOSE_STATUS_CANCELLED -> sb.append("CANCELLED,")
        }
        // Append the segment references
        sb.append("SEND_SEGM=${sendSegment.value.hexAddress},RCV_SEGM=${receiveSegment.value.hexAddress}")
        if (!isRendezvousOrUnlimited) sb.append(",EB_SEGM=${bufferEndSegment.value.hexAddress}")
        sb.append("  ") // add some space
        // Append the linked list of segments.
        val firstSegment = listOf(receiveSegment.value, sendSegment.value, bufferEndSegment.value)
            .filter { it !== NULL_SEGMENT }
            .minBy { it.id }
        var segment = firstSegment
        while (true) {
            sb.append("${segment.hexAddress}=[${if (segment.isRemoved) "*" else ""}${segment.id},prev=${segment.prev?.hexAddress},")
            repeat(SEGMENT_SIZE) { i ->
                val cellState = segment.getState(i)
                val element = segment.getElement(i)
                val cellStateString = when (cellState) {
                    is CancellableContinuation<*> -> "cont"
                    is SelectInstance<*> -> "select"
                    is ReceiveCatching<*> -> "receiveCatching"
                    is SendBroadcast -> "send(broadcast)"
                    is WaiterEB -> "EB($cellState)"
                    else -> cellState.toString()
                }
                sb.append("[$i]=($cellStateString,$element),")
            }
            sb.append("next=${segment.next?.hexAddress}]  ")
            // Process the next segment if exists.
            segment = segment.next ?: break
        }
        // The string representation of this channel is now constructed!
        return sb.toString()
    }


    // This is an internal methods for tests.
    fun checkSegmentStructureInvariants() {
        if (isRendezvousOrUnlimited) {
            check(bufferEndSegment.value === NULL_SEGMENT) {
                "bufferEndSegment must be NULL_SEGMENT for rendezvous and unlimited channels; they do not manipulate it.\n" +
                    "Channel state: $this"
            }
        } else {
            check(receiveSegment.value.id <= bufferEndSegment.value.id) {
                "bufferEndSegment should not have lower id than receiveSegment.\n" +
                    "Channel state: $this"
            }
        }
        val firstSegment = listOf(receiveSegment.value, sendSegment.value, bufferEndSegment.value)
            .filter { it !== NULL_SEGMENT }
            .minBy { it.id }
        check(firstSegment.prev == null) {
            "All processed segments should be unreachable from the data structure, but the `prev` link of the leftmost segment is non-null.\n" +
                "Channel state: $this"
        }
        // Check that the doubly-linked list of segments does not
        // contain full-of-cancelled-cells segments.
        var segment = firstSegment
        while (segment.next != null) {
            // Note that the `prev` reference can be `null` if this channel is closed.
            check(segment.next!!.prev == null || segment.next!!.prev === segment) {
                "The `segment.next.prev === segment` invariant is violated.\n" +
                    "Channel state: $this"
            }
            // Count the number of closed/interrupted cells
            // and check that all cells are in expected states.
            var interruptedOrClosedCells = 0
            for (i in 0 until SEGMENT_SIZE) {
                when (val state = segment.getState(i)) {
                    BUFFERED -> {} // The cell stores a buffered element.
                    is Waiter -> {} // The cell stores a suspended request.
                    INTERRUPTED_RCV, INTERRUPTED_SEND, CHANNEL_CLOSED -> {
                        // The cell stored an interrupted request or indicates
                        // that this channel is already closed.
                        // Check that the element slot is cleaned and increment
                        // the number of cells in closed/interrupted state.
                        check(segment.getElement(i) == null)
                        interruptedOrClosedCells++
                    }
                    POISONED, DONE_RCV -> {
                        // The cell is successfully processed or poisoned.
                        // Check that the element slot is cleaned.
                        check(segment.getElement(i) == null)
                    }
                    // Other states are illegal after all running operations finish.
                    else -> error("Unexpected segment cell state: $state.\nChannel state: $this")
                }
            }
            // Is this segment full of cancelled/closed cells?
            // If so, this segment should be removed from the
            // linked list if nether `receiveSegment`, nor
            // `sendSegment`, nor `bufferEndSegment` reference it.
            if (interruptedOrClosedCells == SEGMENT_SIZE) {
                check(segment === receiveSegment.value || segment === sendSegment.value || segment === bufferEndSegment.value) {
                    "Logically removed segment is reachable.\nChannel state: $this"
                }
            }
            // Process the next segment.
            segment = segment.next!!
        }
    }
}

/**
 * The channel is represented as a list of segments, which simulates an infinite array.
 * Each segment has its own [id], which increase from the beginning. These [id]s help
 * to update [BufferedChannel.sendSegment], [BufferedChannel.receiveSegment],
 * and [BufferedChannel.bufferEndSegment] correctly.
 */
internal class ChannelSegment<E>(id: Long, prev: ChannelSegment<E>?, channel: BufferedChannel<E>?, pointers: Int) : Segment<ChannelSegment<E>>(id, prev, pointers) {
    private val _channel: BufferedChannel<E>? = channel
    val channel get() = _channel!! // always non-null except for `NULL_SEGMENT`

    private val data = atomicArrayOfNulls<Any?>(SEGMENT_SIZE * 2) // 2 registers per slot: state + element
    override val numberOfSlots: Int get() = SEGMENT_SIZE

    // ########################################
    // # Manipulation with the Element Fields #
    // ########################################

    internal fun storeElement(index: Int, element: E) {
        setElementLazy(index, element)
    }

    @Suppress("UNCHECKED_CAST")
    internal fun getElement(index: Int) = data[index * 2].value as E

    internal fun retrieveElement(index: Int): E = getElement(index).also { cleanElement(index) }

    internal fun cleanElement(index: Int) {
        setElementLazy(index, null)
    }

    private fun setElementLazy(index: Int, value: Any?) {
        data[index * 2].lazySet(value)
    }

    // ######################################
    // # Manipulation with the State Fields #
    // ######################################

    internal fun getState(index: Int): Any? = data[index * 2 + 1].value

    internal fun setState(index: Int, value: Any?) {
        data[index * 2 + 1].value = value
    }

    internal fun casState(index: Int, from: Any?, to: Any?) = data[index * 2 + 1].compareAndSet(from, to)

    internal fun getAndSetState(index: Int, update: Any?) = data[index * 2 + 1].getAndSet(update)


    // ########################
    // # Cancellation Support #
    // ########################

    override fun onCancellation(index: Int, cause: Throwable?) {
        onCancellation(index)
    }

    fun onSenderCancellationWithOnUndeliveredElement(index: Int, context: CoroutineContext) {
        // Read the element first. If the operation has not been successfully resumed
        // (this cancellation may be caused by prompt cancellation during dispatching),
        // it is guaranteed that the element is presented.
        val element = getElement(index)
        // Perform the cancellation; `onCancellationImpl(..)` return `true` if the
        // cancelled operation had not been resumed. In this case, the `onUndeliveredElement`
        // lambda should be called.
        if (onCancellation(index)) {
            channel.onUndeliveredElement!!.callUndeliveredElement(element, context)
        }
    }

    /**
     *  Returns `true` if the request is successfully cancelled,
     *  and no rendezvous has happened. We need this knowledge
     *  to keep [BufferedChannel.onUndeliveredElement] correct.
     */
    @Suppress("ConvertTwoComparisonsToRangeCheck")
    fun onCancellation(index: Int): Boolean {
        // Count the global index of this cell and read
        // the current counters of send and receive operations.
        val globalIndex = id * SEGMENT_SIZE + index
        val s = channel.sendersCounter
        val r = channel.receiversCounter
        // Update the cell state trying to distinguish whether
        // the cancelled coroutine is sender or receiver.
        var isSender: Boolean
        var isReceiver: Boolean
        while (true) { // CAS-loop
            // Read the current state of the cell.
            val cur = data[index * 2 + 1].value
            when {
                // The cell stores a waiter.
                cur is Waiter || cur is WaiterEB -> {
                    // Is the cancelled request send for sure?
                    isSender = globalIndex < s && globalIndex >= r
                    // Is the cancelled request receiver for sure?
                    isReceiver = globalIndex < r && globalIndex >= s
                    // If the cancelled coroutine neither sender
                    // nor receiver, clean the element slot and finish.
                    // An opposite operation will resume this request
                    // and update the cell state eventually.
                    if (!isSender && !isReceiver) {
                        cleanElement(index)
                        return true
                    }
                    // The cancelled request is either send or receive.
                    // Update the cell state correspondingly.
                    val update = if (isSender) INTERRUPTED_SEND else INTERRUPTED_RCV
                    if (data[index * 2 + 1].compareAndSet(cur, update)) break
                }
                // The cell already indicates that the operation is cancelled.
                cur === INTERRUPTED_SEND || cur === INTERRUPTED_RCV -> {
                    // Clean the element slot to avoid memory leaks and finish.
                    cleanElement(index)
                    return true
                }
                // An opposite operation is resuming this request;
                // wait until the cell state updates.
                // It is possible that an opposite operation has already
                // resumed this request, which will result in updating
                // the cell state to `DONE_RCV` or `BUFFERED`, while the
                // current cancellation is caused by prompt cancellation.
                cur === RESUMING_BY_EB || cur === RESUMING_BY_RCV -> continue
                // This request was successfully resumed, so this cancellation
                // is caused by the prompt cancellation feature and should be ignored.
                cur === DONE_RCV || cur === BUFFERED -> return false
                // The cell state indicates that the channel is closed;
                // this cancellation should be ignored.
                cur === CHANNEL_CLOSED -> {
                    return false
                }
                else -> error("unexpected state: $cur")
            }
        }
        // Clean the element slot and invoke `onSlotCleaned()`,
        // which may cause deleting the whole segment from the linked list.
        // In case the cancelled request is receiver, it is critical to ensure
        // that the `expandBuffer()` attempt that processes this cell is completed,
        // so `onCancelledRequest(..)` waits for its completion before invoking `onSlotCleaned()`.
        cleanElement(index)
        onCancelledRequest(index, isReceiver)
        return true
    }

    /**
     * Invokes `onSlotCleaned()` preceded by a `waitExpandBufferCompletion(..)` call
     * in case the cancelled request is receiver.
     */
    fun onCancelledRequest(index: Int, receiver: Boolean) {
        if (receiver) channel.waitExpandBufferCompletion(id * SEGMENT_SIZE + index)
        onSlotCleaned()
    }
}

// WA for atomicfu + JVM_IR compiler bug that lead to SMAP-related compiler crashes: KT-55983
internal fun <E> createSegmentFunction(): KFunction2<Long, ChannelSegment<E>, ChannelSegment<E>> = ::createSegment

private fun <E> createSegment(id: Long, prev: ChannelSegment<E>) = ChannelSegment(
    id = id,
    prev = prev,
    channel = prev.channel,
    pointers = 0
)
private val NULL_SEGMENT = ChannelSegment<Any?>(id = -1, prev = null, channel = null, pointers = 0)

/**
 * Number of cells in each segment.
 */
@JvmField
internal val SEGMENT_SIZE = systemProp("kotlinx.coroutines.bufferedChannel.segmentSize", 32)

/**
 * Number of iterations to wait in [BufferedChannel.waitExpandBufferCompletion] until the numbers of started and completed
 * [BufferedChannel.expandBuffer] calls coincide. When the limit is reached, [BufferedChannel.waitExpandBufferCompletion]
 * blocks further [BufferedChannel.expandBuffer]-s to avoid starvation.
 */
private val EXPAND_BUFFER_COMPLETION_WAIT_ITERATIONS = systemProp("kotlinx.coroutines.bufferedChannel.expandBufferCompletionWaitIterations", 10_000)

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
  If the channel is rendezvous or unlimited, the `bufferEnd` counter
  should be initialized with the corresponding value below and never change.
  In this case, the `expandBuffer(..)` operation does nothing.
 */
private const val BUFFER_END_RENDEZVOUS = 0L // no buffer
private const val BUFFER_END_UNLIMITED = Long.MAX_VALUE // infinite buffer
private fun initialBufferEnd(capacity: Int): Long = when (capacity) {
    Channel.RENDEZVOUS -> BUFFER_END_RENDEZVOUS
    Channel.UNLIMITED -> BUFFER_END_UNLIMITED
    else -> capacity.toLong()
}

/*
  Cell states. The initial "empty" state is represented with `null`,
  and suspended operations are represented with [Waiter] instances.
 */

// The cell stores a buffered element.
@JvmField
internal val BUFFERED = Symbol("BUFFERED")
// Concurrent `expandBuffer(..)` can inform the
// upcoming sender that it should buffer the element.
private val IN_BUFFER = Symbol("SHOULD_BUFFER")
// Indicates that a receiver (RCV suffix) is resuming
// the suspended sender; after that, it should update
// the state to either `DONE_RCV` (on success) or
// `INTERRUPTED_SEND` (on failure).
private val RESUMING_BY_RCV = Symbol("S_RESUMING_BY_RCV")
// Indicates that `expandBuffer(..)` (RCV suffix) is resuming
// the suspended sender; after that, it should update
// the state to either `BUFFERED` (on success) or
// `INTERRUPTED_SEND` (on failure).
private val RESUMING_BY_EB = Symbol("RESUMING_BY_EB")
// When a receiver comes to the cell already covered by
// a sender (according to the counters), but the cell
// is still in `EMPTY` or `IN_BUFFER` state, it breaks
// the cell by changing its state to `POISONED`.
private val POISONED = Symbol("POISONED")
// When the element is successfully transferred
// to a receiver, the cell changes to `DONE_RCV`.
private val DONE_RCV = Symbol("DONE_RCV")
// Cancelled sender.
private val INTERRUPTED_SEND = Symbol("INTERRUPTED_SEND")
// Cancelled receiver.
private val INTERRUPTED_RCV = Symbol("INTERRUPTED_RCV")
// Indicates that the channel is closed.
internal val CHANNEL_CLOSED = Symbol("CHANNEL_CLOSED")
// When the cell is already covered by both sender and
// receiver (`sender` and `receivers` counters are greater
// than the cell number), the `expandBuffer(..)` procedure
// cannot distinguish which kind of operation is stored
// in the cell. Thus, it wraps the waiter with this descriptor,
// informing the possibly upcoming receiver that it should
// complete the `expandBuffer(..)` procedure if the waiter stored
// in the cell is sender. In turn, senders ignore this information.
private class WaiterEB(@JvmField val waiter: Waiter) {
    override fun toString() = "WaiterEB($waiter)"
}



/**
 * To distinguish suspended [BufferedChannel.receive] and
 * [BufferedChannel.receiveCatching] operations, the latter
 * uses this wrapper for its continuation.
 */
private class ReceiveCatching<E>(
    @JvmField val cont: CancellableContinuationImpl<ChannelResult<E>>
) : Waiter by cont

/*
  Internal results for [BufferedChannel.updateCellReceive].
  On successful rendezvous with waiting sender or
  buffered element retrieval, the corresponding element
  is returned as result of [BufferedChannel.updateCellReceive].
 */
private val SUSPEND = Symbol("SUSPEND")
private val SUSPEND_NO_WAITER = Symbol("SUSPEND_NO_WAITER")
private val FAILED = Symbol("FAILED")

/*
  Internal results for [BufferedChannel.updateCellSend]
 */
private const val RESULT_RENDEZVOUS = 0
private const val RESULT_BUFFERED = 1
private const val RESULT_SUSPEND = 2
private const val RESULT_SUSPEND_NO_WAITER = 3
private const val RESULT_CLOSED = 4
private const val RESULT_FAILED = 5

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

/*
  The `senders` counter and the channel close status
  are stored in a single 64-bit register to save the space
  and reduce the number of reads in sending operations.
  The code below encapsulates the required bit arithmetics.
 */
private const val SENDERS_CLOSE_STATUS_SHIFT = 60
private const val SENDERS_COUNTER_MASK = (1L shl SENDERS_CLOSE_STATUS_SHIFT) - 1
private inline val Long.sendersCounter get() = this and SENDERS_COUNTER_MASK
private inline val Long.sendersCloseStatus: Int get() = (this shr SENDERS_CLOSE_STATUS_SHIFT).toInt()
private fun constructSendersAndCloseStatus(counter: Long, closeStatus: Int): Long =
    (closeStatus.toLong() shl SENDERS_CLOSE_STATUS_SHIFT) + counter

/*
  The `completedExpandBuffersAndPauseFlag` 64-bit counter contains
  the number of completed `expandBuffer()` attempts along with a special
  flag that pauses progress to avoid starvation in `waitExpandBufferCompletion(..)`.
  The code below encapsulates the required bit arithmetics.
 */
private const val EB_COMPLETED_PAUSE_EXPAND_BUFFERS_BIT = 1L shl 62
private const val EB_COMPLETED_COUNTER_MASK = EB_COMPLETED_PAUSE_EXPAND_BUFFERS_BIT - 1
private inline val Long.ebCompletedCounter get() = this and EB_COMPLETED_COUNTER_MASK
private inline val Long.ebPauseExpandBuffers: Boolean get() = (this and EB_COMPLETED_PAUSE_EXPAND_BUFFERS_BIT) != 0L
private fun constructEBCompletedAndPauseFlag(counter: Long, pauseEB: Boolean): Long =
    (if (pauseEB) EB_COMPLETED_PAUSE_EXPAND_BUFFERS_BIT else 0) + counter
