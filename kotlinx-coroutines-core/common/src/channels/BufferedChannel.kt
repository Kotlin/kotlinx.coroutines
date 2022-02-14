@file:OptIn(InternalCoroutinesApi::class)

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.ChannelResult.Companion.closed
import kotlinx.coroutines.channels.ChannelResult.Companion.failure
import kotlinx.coroutines.channels.ChannelResult.Companion.success
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.selects.TrySelectDetailedResult.*
import kotlin.coroutines.*
import kotlin.js.*
import kotlin.jvm.*
import kotlin.math.*
import kotlin.native.concurrent.*
import kotlin.random.*
import kotlin.reflect.*

/**
 * TODO huge documentation
 */
internal open class BufferedChannel<E>(
    /**
     * Channel capacity, `0` for rendezvous channel
     * and `Channel.UNLIMITED` for unlimited capacity.
     */
    capacity: Int,
    @JvmField
    protected val onUndeliveredElement: OnUndeliveredElement<E>? = null
) : Channel<E> {
    init {
        require(capacity >= 0) { "Invalid channel capacity: $capacity, should be >=0" }
    }

    /*
      The counters and the segments for send, receive, and buffer expansion operations.
      The counters are incremented in the  beginning of the corresponding operation;
      thus, acquiring a unique (for the operation type) cell to process.
     */
    private val sendersAndCloseStatus = atomic(0L)
    private val receivers = atomic(0L)
    private val bufferEnd = atomic(initialBufferEnd(capacity))

    private val rendezvousOrUnlimited
        get() = bufferEnd.value.let { it == BUFFER_END_RENDEZVOUS || it == BUFFER_END_UNLIMITED }

    private val sendSegment: AtomicRef<ChannelSegment<E>>
    private val receiveSegment: AtomicRef<ChannelSegment<E>>
    private val bufferEndSegment: AtomicRef<ChannelSegment<E>>

    init {
        val s = ChannelSegment<E>(0, null, 3)
        sendSegment = atomic(s)
        receiveSegment = atomic(s)
        bufferEndSegment = atomic(if (rendezvousOrUnlimited) (NULL_SEGMENT as ChannelSegment<E>) else s)
    }

    // #########################
    // ## The send operations ##
    // #########################

    /**
     * This function is invoked when a receiver is stored as a waiter in this channel.
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
     * completes due to element retrieving or discovering this channel in the closed state,
     * or suspends if this channel is empty and not closed. We use this function to
     * protect all receive operations with global lock, by acquiring the lock in the
     * beginning of each receiving operation and releasing it when the synchronization
     * completes, via this function.
     */
    protected open fun onReceiveSynchronizationCompletion() {}

    override fun trySend(element: E): ChannelResult<Unit> {
        // Do not try to send the value when the plain `send(e)` operation should suspend.
        if (shouldSendSuspend(sendersAndCloseStatus.value)) return failure()
        // This channel either has waiting receivers or is closed.
        // Let's try to send the element!
        // The logic is similar to the plain `send(e)` operation, with
        // the only difference that we use a special `INTERRUPTED` token
        // as waiter. Intuitively, in case of suspension (the checks above
        // can become outdated), we insert an already cancelled waiter by
        // putting `INTERRUPTED` to the cell.
        return sendImpl( // <-- this is an inline function
            element = element,
            // Use a special token that represents a cancelled waiter.
            // Consumers cannot resume it and skip the corresponding cell.
            waiter = INTERRUPTED,
            // Finish successfully when a rendezvous happens
            // or the element has been buffered.
            onRendezvousOrBuffered = { success(Unit) },
            // On suspension, the `INTERRUPTED` token has been installed,
            // and this `trySend(e)` fails. According to the contract,
            // we do not need to call [onUndeliveredElement] handler as
            // in the plain `send(e)` operation.
            onSuspend = { _, _ -> failure() },
            // When the channel is closed, return the corresponding result.
            onClosed = { onClosedTrySend() }
        )
    }
    private fun onClosedTrySend(): ChannelResult<Unit> {
        return closed(sendException(getCloseCause()))
    }

    private class SenderBroadcast(val cont: CancellableContinuation<Boolean>) : Waiter

    internal open suspend fun sendBroadcast(element: E): Boolean = suspendCancellableCoroutineReusable { cont ->
        sendImpl(
            element = element,
            waiter = SenderBroadcast(cont),
            onRendezvousOrBuffered = { cont.resume(true) },
            onSuspend = { segm, i -> cont.prepareSenderForSuspension(segm, i) },
            onClosed = { cont.resume(false) }
        )
    }

    private suspend fun trySendFast(element: E) {
        val segm = sendSegment.value
        val curSendersAndCloseStatus = sendersAndCloseStatus.getAndIncrement()
        val s = curSendersAndCloseStatus.counter
        val id = s / SEGMENT_SIZE
        val i = (s % SEGMENT_SIZE).toInt()
        if (curSendersAndCloseStatus.closeStatus == CLOSE_STATUS_ACTIVE && segm.id == id) {
            val state = segm.getState(i)
            if (state == null) {
                segm.storeElement(i, element)
                if (s < bufferEnd.value || s < receivers.value) {
                    if (segm.casState(i, null, BUFFERED)) return
                    segm.cleanElement(i)
                } else {
                    return tryInstallSender(segm, i, element, s)
                }
            } else if (state is Waiter) {
                if (segm.casState(i, state, DONE)) {
                    if (state.tryResumeReceiver(element)) {
                        onReceiveDequeued()
                        return
                    }
                }
            }
        }
        trySendSlow(segm, i, element, s)
    }

    private suspend fun tryInstallSender(segm: ChannelSegment<E>, i: Int, element: E, s: Long)
    = suspendCancellableCoroutineReusable<Unit> sc@ { cont ->
        if (segm.casState(i, null, cont)) return@sc
        tryInstallSender1(segm, i, element, s, cont)
    }

    private fun tryInstallSender1(segm: ChannelSegment<E>, i: Int, element: E, s: Long, cont: CancellableContinuation<Unit>) {
        sendImplOnNoWaiter( // <-- this is an inline function
            segm, i, element, s,
            // Store the created continuation as a waiter.
            waiter = cont,
            // If a rendezvous happens or the element has been buffered,
            // resume the continuation and finish. In case of prompt
            // cancellation, it is guaranteed that the element
            // has been already buffered or passed to receiver.
            onRendezvous = { cont.resume(Unit) },
            // Clean the cell on suspension and invoke
            // `onUndeliveredElement(..)` if needed.
            onSuspend = { segm, i -> cont.prepareSenderForSuspension(segm, i) },
            // Call `onUndeliveredElement(..)` and complete the
            // continuation with the exception this channel
            // has been closed by.
            onClosed = { onClosedSendOnNoWaiterSuspend(element, cont) },
        )
    }

    private suspend fun trySendSlow(segm: ChannelSegment<E>, i: Int, element: E, s: Long) {
        sendImplOnNoWaiter(
            segm, i, element, s,
            waiter = null,
            onRendezvous = {},
            onSuspend = { _, _ -> assert { false } },
            onClosed = { onClosedSend(element, coroutineContext) },
            onNoWaiterSuspend = { segm, i, elem, s -> sendOnNoWaiterSuspend(segm, i, elem, s) }
        )
    }

    private suspend fun send0(element: E): Unit = trySendFast(element)

    override suspend fun send(element: E): Unit = sendImpl( // <-- this is an inline function
        element = element,
        // Do not create continuation until it is required,
        // it is later created via [onNoWaiter] below, if needed.
        waiter = null,
        // Finish immediately when a rendezvous happens
        // or the element has been buffered.
        onRendezvousOrBuffered = {},
        // As no waiter is provided, suspension is impossible.
        onSuspend = { _, _ -> assert { false } },
        // According to the `send(e)` contract, we need to call
        // `onUndeliveredElement(..)` handler and throw exception
        // if the channel is already closed.
        onClosed = { onClosedSend(element, coroutineContext) },
        // When `send(e)` decides to suspend, the corresponding
        // `suspend` function is called -- the tail-call optimization
        // should be applied here.
        onNoWaiterSuspend = { segm, i, elem, s -> sendOnNoWaiterSuspend(segm, i, elem, s) }
    )
    private fun onClosedSend(element: E, coroutineContext: CoroutineContext) {
        onUndeliveredElement?.callUndeliveredElement(element, coroutineContext)
        throw recoverStackTrace(sendException(getCloseCause()))
    }

    private suspend fun sendOnNoWaiterSuspend(
        // The working cell is specified via
        // segment and index in it.
        segment: ChannelSegment<E>,
        i: Int,
        // The element to be inserted.
        element: E,
        // The global index of the working cell.
        s: Long
    ) = suspendCancellableCoroutineReusable<Unit> sc@{ cont ->
        sendImplOnNoWaiter( // <-- this is an inline function
            segment, i, element, s,
            // Store the created continuation as a waiter.
            waiter = cont,
            // If a rendezvous happens or the element has been buffered,
            // resume the continuation and finish. In case of prompt
            // cancellation, it is guaranteed that the element
            // has been already buffered or passed to receiver.
            onRendezvous = { cont.resume(Unit) },
            // Clean the cell on suspension and invoke
            // `onUndeliveredElement(..)` if needed.
            onSuspend = { segm, i -> cont.prepareSenderForSuspension(segm, i) },
            // Call `onUndeliveredElement(..)` and complete the
            // continuation with the exception this channel
            // has been closed by.
            onClosed = { onClosedSendOnNoWaiterSuspend(element, cont) },
        )
    }
    private fun CancellableContinuation<*>.prepareSenderForSuspension(
        // The working cell is specified via
        // segment and index in it.
        segment: ChannelSegment<E>,
        i: Int
    ) {
//        invokeOnCancellation {
//            // Clean the cell on suspension and invoke `onUndeliveredElement(..)`
//            // if the continuation is still stored in the cell.
//            segment.onCancellation(i, onUndeliveredElement, context)
//        }
    }
    private fun onClosedSendOnNoWaiterSuspend(element: E, cont: CancellableContinuation<Unit>) {
        onUndeliveredElement?.callUndeliveredElement(element, cont.context)
        cont.resumeWithException(recoverStackTrace(sendException(getCloseCause()), cont))
    }

    /**
     * Checks whether a [send] invocation is bound to suspend if it is called
     * with the specified [sendersAndCloseStatus] value, the current [receivers]
     * and [bufferEnd] counters. When this channel is already closed, the function
     * returns `false`.
     *
     * Specifically, [send] suspends if the channel is NOT unlimited,
     * the number of receivers is greater than then index of the working cell of the
     * potential [send] invocation, and the buffer does not cover this cell
     * in case of buffered channel.
     */
    @JsName("shouldSendSuspend0")
    private fun shouldSendSuspend(curSendersAndCloseStatus: Long): Boolean {
        if (curSendersAndCloseStatus.isClosedForSend0) return false
        return !bufferOrRendezvousSend(curSendersAndCloseStatus.counter)
    }
    private fun bufferOrRendezvousSend(curSenders: Long): Boolean =
         curSenders < bufferEnd.value || curSenders < receivers.value
    /**
     * Checks whether a [send] invocation is bound to suspend if it is called
     * with the current counter and closing status values. See [shouldSendSuspend].
     */
    internal open fun shouldSendSuspend(): Boolean = shouldSendSuspend(sendersAndCloseStatus.value)

    /**
     * Abstract send implementation.
     */
    private inline fun <W, R> sendImpl(
        // The element to be sent.
        element: E,
        // The waiter to be stored in case of suspension,
        // or `null` if the waiter is not created yet.
        // In the latter case, if the algorithm decides
        // to suspend, [onNoWaiterSuspend] is called.
        waiter: W,
        // This lambda is invoked when the element has been
        // buffered or a rendezvous with receiver happens.
        onRendezvousOrBuffered: () -> R,
        // This lambda is called when the operation suspends
        // in the cell specified by the segment and the index in it.
        onSuspend: (segm: ChannelSegment<E>, i: Int) -> R,
        // This lambda is called when the channel
        // is observed in the closed state.
        onClosed: () -> R,
        // This lambda is invoked when the operation decides
        // to suspend, but the waiter is not provided. It should
        // create a waiter and delegate to `sendImplOnNoWaiter`.
        onNoWaiterSuspend: (segm: ChannelSegment<E>, i: Int, element: E, s: Long) -> R
                    = { _, _, _, _ -> error("unreachable code") }
    ): R {
        // Read the segment index first,
        // before the counter increment.
        var segm = sendSegment.value
        while (true) {
            // Atomically increment `senders` counter and obtain the
            // value before the increment and the close status.
            val sendersAndCloseStatusCur = sendersAndCloseStatus.getAndIncrement()
            val s = sendersAndCloseStatusCur.counter

            val closed = sendersAndCloseStatusCur.isClosedForSend0
            // Count the required segment id and the cell index in it.
            val id = s / SEGMENT_SIZE
            val i = (s % SEGMENT_SIZE).toInt()
            // Try to find the required segment if the previously read
            // segment (in the beginning of this function) has lower id.
            if (segm.id != id) {
                // Find the required segment.
                segm = findSegmentSend(id, segm) ?:
                    // The segment has not been found.
                    if (closed) return onClosed() else continue
            }

            when(updateCellSend(segm, i, element, s, if (closed) INTERRUPTED else waiter)) {
                RESULT_RENDEZVOUS -> {
                    segm.cleanPrev()
                    return onRendezvousOrBuffered()
                }
                RESULT_BUFFERED -> {
                    return onRendezvousOrBuffered()
                }
                RESULT_SUSPEND -> {
                    if (closed) return onClosed()
                    return onSuspend(segm, i)
                }
                RESULT_FAILED -> {
                    segm.cleanPrev()
                    if (closed) return onClosed()
                    continue
                }
                RESULT_NO_WAITER -> {
                    return onNoWaiterSuspend(segm, i, element, s)
                }
            }
        }
    }

    private inline fun <R, W> sendImplOnNoWaiter(
        // The working cell is specified via
        // segment and index in it.
        segment: ChannelSegment<E>,
        index: Int,
        // The element to be sent.
        element: E,
        s: Long,
        // The waiter to be stored in case of suspension.
        waiter: W,
        onRendezvous: () -> R,
        onSuspend: (segm: ChannelSegment<E>, i: Int) -> R,
        onClosed: () -> R,
        onNoWaiterSuspend: (segm: ChannelSegment<E>, i: Int, element: E, s: Long) -> R
        = { _, _, _, _ -> error("unreachable code") }
    ): R {
//        val closed = sendersAndCloseStatus.value.isClosedForSend0
//        // Count the required segment id and the cell index in it.
//        val id = s / SEGMENT_SIZE
//        // Try to find the required segment if the previously read
//        // segment (in the beginning of this function) has lower id.
//        var segment = segment
//        if (segment.id != id) {
//            // Find the required segment.
//            segment = findSegmentSend(id, segment) ?:
//                // The segment has not been found.
//                if (closed) return onClosed() else segment
//        }

//        if (segment.id == id) {
            when (updateCellSend(segment, index, element, s, waiter)) {
                RESULT_RENDEZVOUS -> {
                    segment.cleanPrev()
                    return onRendezvous()
                }
                RESULT_BUFFERED -> {
                    return onRendezvous()
                }
                RESULT_SUSPEND -> {
                    return onSuspend(segment, index)
                }
                RESULT_NO_WAITER -> {
                    return onNoWaiterSuspend(segment, index, element, s)
                }
            }
//        }
        return sendImpl(
            element = element,
            waiter = waiter,
            onRendezvousOrBuffered = onRendezvous,
            onSuspend = onSuspend,
            onClosed = onClosed,
            onNoWaiterSuspend = onNoWaiterSuspend
        )
    }

    private fun <W> updateCellSend(
        // The working cell is specified via
        // segment and index in it.
        segment: ChannelSegment<E>,
        index: Int,
        // The element to be sent.
        element: E,
        s: Long,
        waiter: W,
    ): Int {
        segment.storeElement(index, element)
        val b = bufferEnd.value
        if (b == BUFFER_END_RENDEZVOUS || b == BUFFER_END_UNLIMITED) {
            val buffer = b == BUFFER_END_UNLIMITED || s < receivers.value
            if (!buffer && waiter == null) return RESULT_NO_WAITER
            val state = segment.getAndSetState(index, if (buffer) BUFFERED else waiter)
            when {
                state === null -> {
                    return if (buffer) RESULT_BUFFERED else RESULT_SUSPEND
                }
                state is Waiter -> {
                    segment.setStateLazy(index, BROKEN)
                    segment.cleanElement(index)
                    return if (state.tryResumeReceiver(element)) {
                        onReceiveDequeued()
                        RESULT_RENDEZVOUS
                    } else RESULT_FAILED
                }
                state === BROKEN || state === INTERRUPTED || state === CHANNEL_CLOSED -> return RESULT_FAILED
            }
        }
        val curState = segment.getState(index)
        when {
            curState === null -> {
                if (bufferOrRendezvousSend(s)) {
                    if (segment.casState(index, null, BUFFERED)) {
                        return RESULT_BUFFERED
                    }
                } else {
                    if (waiter == null) {
                        return RESULT_NO_WAITER
                    }
                    if (segment.casState(index, null, waiter)) return RESULT_SUSPEND
                }
            }
            curState is Waiter -> {
                segment.cleanElement(index)
                segment.setStateLazy(index, DONE)
                return if (curState.tryResumeReceiver(element)) {
                    onReceiveDequeued()
                    RESULT_RENDEZVOUS
                } else RESULT_FAILED
            }
        }
        return updateCellSendSlow(segment, index, element, s, waiter)
    }

    /**
     * The full algorithm that updates the working cell for
     * an abstract send operation. A fast-path version which
     * is shorter and better for inlining, is available in
     * [updateCellSend] -- it delegates to this full version
     * if the fast path fails.
     */
    private fun <W> updateCellSendSlow(
        // The working cell is specified via
        // segment and index in it.
        segment: ChannelSegment<E>,
        index: Int,
        // The element to be sent.
        element: E,
        s: Long,
        waiter: W,
    ): Int {
        // First, the algorithm stores the element.
        segment.storeElement(index, element)
        // The, the cell state should be updated
        // according to the state machine.
        while (true) {
            // Read the current state.
            val state = segment.getState(index)
            when {
                // The cell is empty.
                state === null -> {
                    // If the element should be buffered, ar a rendezvous should happen
                    // but the receiver is still coming, try to buffer the element.
                    // Otherwise, try to store the specified waiter in the cell.
                    if (bufferOrRendezvousSend(s)) {
                        // Move the cell state to BUFFERED.
                        if (segment.casState(index, null, BUFFERED)) {
                            // The element has been successfully buffered, finish.
                            return if (s < receivers.value) RESULT_RENDEZVOUS else RESULT_BUFFERED
                        }
                    } else {
                        // This send operation should suspend.
                        if (waiter === null) {
                            // The waiter is not specified; clean the element
                            // slot and return the corresponding result.
                            segment.cleanElement(index)
                            return RESULT_NO_WAITER
                        }
                        // Try to install the waiter.
                        if (segment.casState(index, null, waiter)) return RESULT_SUSPEND
                    }
                }
                // The buffer has been expanded and this cell
                // is covered by the buffer. Therefore, the algorithm
                // tries to buffer the element.
                state === SHOULD_BUFFER -> {
                    // Move the state to BUFFERED.
                    if (segment.casState(index, state, BUFFERED))
                        return if (s < receivers.value) RESULT_RENDEZVOUS else RESULT_BUFFERED
                }
                // Fail if the cell is broken by a concurrent receiver,
                // or the receiver stored in this cell was interrupted.
                // or the channel is closed.
                state === BROKEN || state === INTERRUPTED || state === INTERRUPTED_EB || state === INTERRUPTED_R || state === CHANNEL_CLOSED -> {
                    // Clean the element slot to avoid memory leaks.
                    segment.cleanElement(index)
                    return RESULT_FAILED
                }
                state === DONE -> return RESULT_FAILED
                // A waiting receiver is stored in the cell.
                else -> {
                    // Try to move the cell state to DONE.
                    segment.setStateLazy(index, DONE)
                    // As the element passes directly to the waiter,
                    // we should clean the corresponding slot.
                    segment.cleanElement(index)
                    // Unwrap the waiting receiver from `WaiterEB` if needed.
                    val receiver = if (state is WaiterEB) state.waiter else state
                    // Try to make a rendezvous with the receiver.
                    return if (receiver.tryResumeReceiver(element)) {
                        onReceiveDequeued()
                        RESULT_RENDEZVOUS
                    } else RESULT_FAILED
                }
            }
        }
    }

    /**
     * Tries to resume this receiver with the specified
     * [element] as the result. Returns `true` on success,
     * and `false` otherwise.
     */
    private fun Any.tryResumeReceiver(element: E): Boolean = when(this) {
        is SelectInstance<*> -> {
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
        is CancellableContinuation<*> -> {
            this as CancellableContinuation<E>
            tryResume0(element, onUndeliveredElement?.bindCancellationFun(element, context))
        }
        else -> error("Unexpected waiter: $this")
    }


    // ##########################
    // # The receive operations #
    // ##########################

    override suspend fun receive(): E = receiveImpl(
        waiter = null,
        onRendezvous = { element ->
            onReceiveSynchronizationCompletion()
            return element
        },
        onSuspend = { _, _ -> error("unexpected") },
        onClosed = {
            onClosedReceive()
        },
        onNoWaiter = { segm, i, r ->
            receiveOnNoWaiterSuspend(segm, i, r)
        }
    )
    private fun onClosedReceive(): E =
        throw recoverStackTrace(receiveException(getCloseCause())).also { onReceiveSynchronizationCompletion() }

    private suspend fun receiveOnNoWaiterSuspend(
        segm: ChannelSegment<E>,
        i: Int,
        r: Long
    ) = suspendCancellableCoroutineReusable<E> { cont ->
        receiveImplOnNoWaiter(
            segm, i, r,
            waiter = cont,
            onRendezvous = { element ->
                onReceiveSynchronizationCompletion()
                cont.resume(element) {
                    onUndeliveredElement?.callUndeliveredElement(element, cont.context)
                }
            },
            onSuspend = { segm, i ->
                onReceiveEnqueued()
                onReceiveSynchronizationCompletion()
            },
            onClosed = {
                onReceiveSynchronizationCompletion()
                cont.resumeWithException(receiveException(getCloseCause()))
            },
        )
    }

    override suspend fun receiveCatching(): ChannelResult<E> = receiveImpl(
        waiter = null,
        onRendezvous = { element -> onReceiveSynchronizationCompletion(); success(element) },
        onSuspend = { _, _ -> error("unexcepted") },
        onClosed = { onClosedReceiveCatching() },
        onNoWaiter = { segm, i, r -> receiveCatchingOnNoWaiterSuspend(segm, i, r) }
    )

    private fun onClosedReceiveCatching(): ChannelResult<E> =
        closed<E>(getCloseCause()).also { onReceiveSynchronizationCompletion() }

    private suspend fun receiveCatchingOnNoWaiterSuspend(
        segm: ChannelSegment<E>,
        i: Int,
        r: Long
    ) = suspendCancellableCoroutineReusable<ChannelResult<E>> { cont ->
        val waiter = ReceiveCatching(cont)
        receiveImplOnNoWaiter(
            segm, i, r,
            waiter = waiter,
            onRendezvous = { element ->
                onReceiveSynchronizationCompletion()
                cont.resume(success(element)) {
                    onUndeliveredElement?.callUndeliveredElement(element, cont.context)
                }
            },
            onSuspend = { segm, i ->
                onReceiveEnqueued()
                onReceiveSynchronizationCompletion()
//                cont.invokeOnCancellation {
//                    segm.onCancellation(i);
//                    onReceiveDequeued()
//                }
            },
            onClosed = {
                onReceiveSynchronizationCompletion()
                cont.resume(closed(getCloseCause()))
            },
        )
    }

    override fun tryReceive(): ChannelResult<E> =
        tryReceiveInternal().also { onReceiveSynchronizationCompletion() }

    protected fun tryReceiveInternal(): ChannelResult<E> {
        // Read `receivers` counter first.
        val r = receivers.value
        val sendersAndCloseStatusCur = sendersAndCloseStatus.value
        // Is this channel is closed for send?
        if (sendersAndCloseStatusCur.isClosedForReceive0) return onClosedTryReceive()
        // COMMENTS
        val s = sendersAndCloseStatusCur.counter
        if (r >= s) return failure()
        return receiveImpl(
            waiter = INTERRUPTED,
            onRendezvous = { element -> success(element) },
            onSuspend = { _, _ -> failure() },
            onClosed = { onClosedTryReceive() }
        )
    }

    private fun onClosedTryReceive(): ChannelResult<E> =
        closed(getCloseCause())

    private inline fun <R> receiveImpl(
        waiter: Any?,
        onRendezvous: (element: E) -> R,
        onSuspend: (segm: ChannelSegment<E>, i: Int) -> R,
        onClosed: () -> R,
        onNoWaiter: (
            segm: ChannelSegment<E>,
            i: Int,
            r: Long
        ) -> R = { _, _, _ -> error("unexpected") }
    ): R {
        var segm = receiveSegment.value
        while (true) {
            if (sendersAndCloseStatus.value.closeStatus == CLOSE_STATUS_CANCELLED)
                return onClosed()
            val r = this.receivers.getAndIncrement()
            val id = r / SEGMENT_SIZE
            val i = (r % SEGMENT_SIZE).toInt()
            if (segm.id != id) {
                val findSegmResult = findSegmentReceive(id, segm)
                if (findSegmResult.isClosed) {
                    return onClosed()
                }
                segm = findSegmResult.segment
                if (segm.id != id) continue
            }
            val result = updateCellReceive(segm, i, r, waiter)
            when {
                result === SUSPEND -> {
                    return onSuspend(segm, i)
                }
                result === FAILED -> {
                    continue
                }
                result !== NO_WAITER -> { // element
                    segm.cleanPrev()
                    return onRendezvous(result as E)
                }
                result === NO_WAITER -> {
                    return onNoWaiter(segm, i, r)
                }
            }
        }
    }

    private inline fun <W, R> receiveImplOnNoWaiter(
        segm: ChannelSegment<E>,
        i: Int,
        r: Long,
        waiter: W,
        onRendezvous: (element: E) -> R,
        onSuspend: (segm: ChannelSegment<E>, i: Int) -> R,
        onClosed: () -> R
    ): R {
        val result = updateCellReceive(segm, i, r, waiter)
        when {
            result === SUSPEND -> {
                return onSuspend(segm, i)
            }
            result === FAILED -> {
                return receiveImpl(
                    waiter = waiter,
                    onRendezvous = onRendezvous,
                    onSuspend = onSuspend,
                    onClosed = onClosed
                )
            }
            else -> {
                segm.cleanPrev()
                return onRendezvous(result as E)
            }
        }
    }

    private fun updateCellReceive(
        segment: ChannelSegment<E>,
        i: Int,
        r: Long,
        waiter: Any?,
    ): Any? {
        if (rendezvousOrUnlimited) {
            val rendezvous = r < sendersCounter
            if (!rendezvous && waiter == null) return NO_WAITER
            val state = segment.getAndSetState(i, if (rendezvous) BROKEN else waiter)
            when {
                state === null -> {
                    return if (rendezvous) FAILED else SUSPEND
                }
                state === BUFFERED -> {
                    if (!rendezvous) segment.setStateLazy(i, BROKEN)
                    return segment.retrieveElement(i)
                }
                state is Waiter -> {
                    if (!rendezvous) segment.setStateLazy(i, BROKEN)
                    return if (state.tryResumeSender(segment, i)) {
                        return segment.retrieveElement(i)
                    } else {
                        FAILED
                    }
                }
            }
        }
        val curState = segment.getState(i)
        when {
            curState === BUFFERED -> {
                if (segment.casState(i, curState, DONE)) {
                    val element = segment.retrieveElement(i)
                    expandBuffer()
                    return element
                }
            }
            curState === null -> {
                if (waiter == null) return NO_WAITER
                val sendersAndCloseStatusCur = sendersAndCloseStatus.value
                if (sendersAndCloseStatusCur.closeStatus == CLOSE_STATUS_ACTIVE &&
                    r >= sendersAndCloseStatusCur.counter &&
                    segment.casState(i, curState, waiter)
                ) {
                    expandBuffer()
                    return SUSPEND
                }
            }
            curState is Waiter -> if (segment.casState(i, curState, RESUMING_R)) {
                return if (curState.tryResumeSender(segment, i)) {
                    segment.setState(i, DONE)
                    expandBuffer()
                    return segment.retrieveElement(i)
                } else {
                    onSenderResumptionFailure(segment, i, false)
                    FAILED
                }
            }
        }
        return updateCellReceiveSlow(segment, i, r, waiter)
    }

    private fun updateCellReceiveSlow(
        segment: ChannelSegment<E>,
        i: Int,
        r: Long,
        waiter: Any?,
    ): Any? {
        while (true) {
            val state = segment.getState(i)
            when {
                state === null || state === SHOULD_BUFFER -> {
                    val sendersAndCloseStatusCur = sendersAndCloseStatus.value
                    if (sendersAndCloseStatusCur.isClosedForReceive0) {
                        segment.casState(i, state, CHANNEL_CLOSED)
                        continue
                    }
                    if (r < sendersAndCloseStatusCur.counter) {
                        if (segment.casState(i, state, BROKEN)) {
                            expandBuffer()
                            return FAILED
                        }
                    } else {
                        if (waiter === null) return NO_WAITER
                        if (segment.casState(i, state, waiter)) {
                            expandBuffer()
                            return SUSPEND
                        }
                    }
                }
                state === BUFFERED -> {
                    if (segment.casState(i, state, DONE)) {
                        val element = segment.retrieveElement(i)
                        expandBuffer()
                        return element
                    }
                }
                state === INTERRUPTED -> {
                    if (segment.casState(i, state, INTERRUPTED_R)) return FAILED
                }
                state === INTERRUPTED_EB -> {
                    expandBuffer()
                    return FAILED
                }
                state === INTERRUPTED_R -> return FAILED
                state === BROKEN -> return FAILED
                state === CHANNEL_CLOSED -> return FAILED
                state === RESUMING_EB -> continue // spin-wait
                else -> {
                    if (segment.casState(i, state, RESUMING_R)) {
                        val helpExpandBuffer = state is WaiterEB
                        val sender = if (state is WaiterEB) state.waiter else state
                        if (sender.tryResumeSender(segment, i)) {
                            segment.setState(i, DONE)
                            return segment.retrieveElement(i).also { expandBuffer() }
                        } else {
                            onSenderResumptionFailure(segment, i, helpExpandBuffer)
                            return FAILED
                        }
                    }
                }
            }
        }
    }

    private fun onSenderResumptionFailure(
        segment: ChannelSegment<E>,
        i: Int,
        helpExpandBuffer: Boolean
    ) {
        if (!segment.casState(i, RESUMING_R, INTERRUPTED_R) || helpExpandBuffer)
            expandBuffer()
    }

    private fun Any.tryResumeSender(segment: ChannelSegment<E>, i: Int): Boolean = when {
        this is SelectInstance<*> -> {
            this as SelectImplementation<*>
            when (this.trySelectDetailed(this@BufferedChannel, Unit)) {
                SUCCESSFUL -> true
                REREGISTER -> {
                    false
                }
                ALREADY_SELECTED, CANCELLED -> {
                    onUndeliveredElement?.invoke(segment.retrieveElement(i))
                    false
                }
            }
        }
        this is CancellableContinuation<*> -> {
            this as CancellableContinuation<Unit>
            tryResume(Unit).let {
                if (it !== null) {
                    completeResume(it)
                    true
                } else {
                    onUndeliveredElement?.invoke(segment.retrieveElement(i))
                    false
                }
            }
        }
        this is SenderBroadcast -> {
            cont.tryResume(true).let {
                if (it !== null) {
                    cont.completeResume(it)
                    true
                } else {
                    false
                }
            }
        }
        else -> error("Unexpected waiter: $this")
    }

    private fun expandBuffer() {
        if (rendezvousOrUnlimited) return
        var segment = bufferEndSegment.value
        try_again@ while (true) {
            val b = bufferEnd.getAndIncrement()
            val s = sendersAndCloseStatus.value.counter
            val id = b / SEGMENT_SIZE
            if (s <= b) {
                if (segment.id < id) {
                    while (true) {
                        val ss = findSegmentBufferOrLast(id, segment)
                        if (bufferEndSegment.moveForward(ss)) return
                    }
                } // to avoid memory leaks
                return
            }
            val i = (b % SEGMENT_SIZE).toInt()
            if (segment.id != id) {
                segment = findSegmentBuffer(id, segment).let {
                    if (it.isClosed) return else it.segment
                }
            }
            if (segment.id != id) {
                if (receivers.value > b) return
                bufferEnd.compareAndSet(b + 1, segment.id * SEGMENT_SIZE)
                continue@try_again
            }
            if (updateCellExpandBuffer(segment, i, b)) return
        }
    }

    private fun findSegmentBufferOrLast(id: Long, startFrom: ChannelSegment<E>): ChannelSegment<E> {
        var cur: ChannelSegment<E> = startFrom
        while (cur.id < id) {
            cur = cur.next ?: break
        }
        while (cur.removed) {
            cur = cur.next ?: break
        }
        return cur
    }

    private fun updateCellExpandBuffer(
        segm: ChannelSegment<E>,
        i: Int,
        b: Long
    ): Boolean {
        val state = segm.getState(i)
        if (state is Waiter && b >= receivers.value) {
            if (segm.casState(i, state, RESUMING_EB)) {
                return if (state.tryResumeSender(segm, i)) {
                    segm.setState(i, BUFFERED)
                    true
                } else {
                    segm.setState(i, INTERRUPTED)
                    false
                }
            }
        }
        return updateCellExpandBufferSlow(segm, i, b)
    }

    private fun updateCellExpandBufferSlow(
        segm: ChannelSegment<E>,
        i: Int,
        b: Long
    ): Boolean {
        while (true) {
            val state = segm.getState(i)
            when {
                state === null -> {
                    if (segm.casState(i, state, SHOULD_BUFFER)) return true
                }
                state === BUFFERED || state === BROKEN || state === DONE || state === CHANNEL_CLOSED -> return true
                state === RESUMING_R -> if (segm.casState(i, state, RESUMING_R_EB)) return true
                state === INTERRUPTED -> {
                    if (b >= receivers.value) return false
                    if (segm.casState(i, state, INTERRUPTED_EB)) return true
                }
                state === INTERRUPTED_R -> return false
                else -> {
                    check(state is Waiter || state is WaiterEB)
                    if (b < receivers.value) {
                        if (segm.casState(i, state, WaiterEB(waiter = state))) return true
                    } else {
                        if (segm.casState(i, state, RESUMING_EB)) {
                            return if (state.tryResumeSender(segm, i)) {
                                segm.setState(i, BUFFERED)
                                true
                            } else {
                                segm.setState(i, INTERRUPTED)
                                false
                            }
                        }
                    }
                }
            }
        }
    }


    // #######################
    // ## Select Expression ##
    // #######################

    override val onSend: SelectClause2<E, BufferedChannel<E>>
        get() = SelectClause2Impl(
            clauseObject = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForSend as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectSend as ProcessResultFunction
        )

    override val onReceive: SelectClause1<E>
        get() = SelectClause1Impl(
            clauseObject = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectReceive as ProcessResultFunction,
            onCancellationConstructor = onUndeliveredElementReceiveCancellationConstructor
        )

    override val onReceiveCatching: SelectClause1<ChannelResult<E>>
        get() = SelectClause1Impl(
            clauseObject = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectReceiveCatching as ProcessResultFunction,
            onCancellationConstructor = onUndeliveredElementReceiveCancellationConstructor
        )

    protected open fun registerSelectForSend(select: SelectInstance<*>, element: Any?) {
        sendImpl(
            element = element as E,
            waiter = select,
            onRendezvousOrBuffered = { select.selectInRegistrationPhase(Unit) },
            onSuspend = { segm, i ->
                select.disposeOnCompletion {
                    segm.onCancellation(i, onUndeliveredElement, select.context)
                }
            },
            onClosed = {
                select.selectInRegistrationPhase(CHANNEL_CLOSED)
            }
        )
    }

    protected open fun registerSelectForReceive(select: SelectInstance<*>, ignoredParam: Any?) {
        receiveImpl(
            waiter = select,
            onRendezvous = { elem ->
                onReceiveSynchronizationCompletion()
                select.selectInRegistrationPhase(elem)
           },
            onSuspend = { segm, i ->
                onReceiveEnqueued()
                onReceiveSynchronizationCompletion()
                select.disposeOnCompletion { segm.onCancellation(i) }
            },
            onClosed = {
                onReceiveSynchronizationCompletion()
                select.selectInRegistrationPhase(CHANNEL_CLOSED)
            }
        )
    }

    private fun processResultSelectSend(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CHANNEL_CLOSED) throw sendException(getCloseCause())
        else this

    private fun processResultSelectReceive(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CHANNEL_CLOSED) throw receiveException(getCloseCause())
        else selectResult

    private fun processResultSelectReceiveOrNull(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CHANNEL_CLOSED) {
            if (closeCause.value !== null) throw receiveException(getCloseCause())
            null
        } else selectResult

    private fun processResultSelectReceiveCatching(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CHANNEL_CLOSED) closed(closeCause.value as Throwable?)
        else success(selectResult as E)

    private val onUndeliveredElementReceiveCancellationConstructor: OnCancellationConstructor? = onUndeliveredElement?.let {
        { select: SelectInstance<*>, _: Any?, element: Any? ->
            { if (element !== CHANNEL_CLOSED) onUndeliveredElement.callUndeliveredElement(element as E, select.context) }
        }
    }

    // ##############################
    // ## Closing and Cancellation ##
    // ##############################

    /**
     * Indicates whether this channel is cancelled. In case it is cancelled,
     * it stores either an exception if it was cancelled with or `null` if
     * this channel was cancelled without error. Stores [NO_CLOSE_CAUSE] if this
     * channel is not cancelled.
     */
    private val closeCause = atomic<Any?>(NO_CLOSE_CAUSE)

    protected fun getCloseCause() = closeCause.value as Throwable?

    private fun receiveException(cause: Throwable?) =
        cause ?: ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)
    protected fun sendException(cause: Throwable?) =
        cause ?: ClosedSendChannelException(DEFAULT_CLOSE_MESSAGE)

    // Stores the close handler.
    private val closeHandler = atomic<Any?>(null)

    private fun markClosed(): Unit =
        sendersAndCloseStatus.update { cur ->
            when (cur.closeStatus) {
                CLOSE_STATUS_ACTIVE ->
                    constructSendersAndCloseStatus(cur.counter, CLOSE_STATUS_CLOSED)
                CLOSE_STATUS_CANCELLATION_STARTED ->
                    constructSendersAndCloseStatus(cur.counter, CLOSE_STATUS_CANCELLED)
                else -> return
            }
        }.also { check(closeCause.value is Throwable?) }

    private fun markCancelled(): Unit =
        sendersAndCloseStatus.update { cur ->
            constructSendersAndCloseStatus(cur.counter, CLOSE_STATUS_CANCELLED)
        }

    private fun markCancellationStarted(): Unit =
        sendersAndCloseStatus.update { cur ->
            if (cur.closeStatus == CLOSE_STATUS_ACTIVE)
                constructSendersAndCloseStatus(cur.counter, CLOSE_STATUS_CANCELLATION_STARTED)
            else return
        }

    private fun completeCloseOrCancel() {
        sendersAndCloseStatus.value.isClosedForSend0
    }

    override fun close(cause: Throwable?): Boolean = closeImpl(cause, false)

    protected open fun closeImpl(cause: Throwable?, cancel: Boolean): Boolean {
        if (cancel) markCancellationStarted()
        val closedByThisOperation = closeCause.compareAndSet(NO_CLOSE_CAUSE, cause)
        if (cancel) markCancelled() else markClosed()
        completeCloseOrCancel()
        return if (closedByThisOperation) {
            invokeCloseHandler()
            true
        } else false
    }

    private fun completeClose(sendersCur: Long) {
        val segm = closeQueue()
        removeWaitingRequests(segm, sendersCur)
        onClosedIdempotent()
    }

    private fun completeCancel(sendersCur: Long) {
        completeClose(sendersCur)
        removeRemainingBufferedElements()
    }

    private fun closeQueue(): ChannelSegment<E> {
        // Choose the last segment.
        var lastSegment = bufferEndSegment.value
        sendSegment.value.let {
            if (it.id > lastSegment.id) lastSegment = it
        }
        receiveSegment.value.let {
            if (it.id > lastSegment.id) lastSegment = it
        }
        // Close the linked list of segment for new segment addition
        // and return the last segment at the point of closing.
        return lastSegment.close()
    }

    private fun invokeCloseHandler() {
        val closeHandler = closeHandler.getAndUpdate {
            if (it === null) CLOSE_HANDLER_CLOSED
            else CLOSE_HANDLER_INVOKED
        } ?: return
        closeHandler as (cause: Throwable?) -> Unit
        val closeCause = closeCause.value as Throwable?
        closeHandler(closeCause)
    }

    override fun invokeOnClose(handler: (cause: Throwable?) -> Unit) {
        if (closeHandler.compareAndSet(null, handler)) {
            // Handler has been successfully set, finish the operation.
            return
        }
        // Either handler was set already or this channel is cancelled.
        // Read the value of [closeHandler] and either throw [IllegalStateException]
        // or invoke the handler respectively.
        when (val curHandler = closeHandler.value) {
            CLOSE_HANDLER_CLOSED -> {
                // In order to be sure that our handler is the only one, we have to change the
                // [closeHandler] value to `INVOKED`. If this CAS fails, another handler has been
                // executed and an [IllegalStateException] should be thrown.
                if (closeHandler.compareAndSet(CLOSE_HANDLER_CLOSED, CLOSE_HANDLER_INVOKED)) {
                    handler(closeCause.value as Throwable?)
                } else {
                    throw IllegalStateException("Another handler was already registered and successfully invoked")
                }
            }
            CLOSE_HANDLER_INVOKED -> {
                throw IllegalStateException("Another handler was already registered and successfully invoked")
            }
            else -> {
                throw IllegalStateException("Another handler was already registered: $curHandler")
            }
        }
    }

    /**
     * Invoked when channel is closed as the last action of [close] invocation.
     * This method should be idempotent and can be called multiple times.
     */
    protected open fun onClosedIdempotent() {}

    protected open fun onCancel(wasClosed: Boolean) {}

    final override fun cancel(cause: Throwable?): Boolean = cancelImpl(cause)
    final override fun cancel() { cancelImpl(null) }
    final override fun cancel(cause: CancellationException?) { cancelImpl(cause) }

    internal open fun cancelImpl(cause: Throwable?): Boolean {
        val cause = cause ?: CancellationException("Channel was cancelled")
        val wasClosed = closeImpl(cause, true)
        removeRemainingBufferedElements()
        onCancel(wasClosed)
        return wasClosed
    }

    private fun removeRemainingBufferedElements() {
        // clear buffer first, but do not wait for it in helpers
        val onUndeliveredElement = onUndeliveredElement
        var undeliveredElementException: UndeliveredElementException? = null // first cancel exception, others suppressed

        var segm: ChannelSegment<E> = sendSegment.value
        while (true) {
            segm = segm.next ?: break
        }
        while (true) {
            val segmPrev = segm.prev
            for (i in SEGMENT_SIZE - 1 downTo 0) {
                if (segm.id * SEGMENT_SIZE + i < receivers.value) return
                while (true) {
                    val state = segm.getState(i)
                    when {
                        state === BUFFERED -> if (segm.casState(i, state, CHANNEL_CLOSED)) {
                            if (onUndeliveredElement != null) {
                                undeliveredElementException = onUndeliveredElement.callUndeliveredElementCatchingException(segm.retrieveElement(i), undeliveredElementException)
                            }
                            segm.onCancellation(i)
                            break
                        }
                        state === SHOULD_BUFFER || state === null -> if (segm.casState(i, state, CHANNEL_CLOSED)) {
                            segm.onCancellation(i)
                            break
                        }
                        state is Waiter -> {
                            if (segm.casState(i, state, CHANNEL_CLOSED)) {
                                state.closeSender()
                                break
                            }
                        }
                        state is WaiterEB -> {
                            if (segm.casState(i, state, CHANNEL_CLOSED)) {
                                state.waiter.closeSender()
                                break
                            }
                        }
                        else -> break
                    }
                }
            }
            segm = segmPrev ?: break
        }
        undeliveredElementException?.let { throw it } // throw UndeliveredElementException at the end if there was one
    }

    private fun removeWaitingRequests(lastSegment: ChannelSegment<E>, sendersCur: Long) {
        var segm: ChannelSegment<E>? = lastSegment
        while (segm != null) {
            for (i in SEGMENT_SIZE - 1 downTo 0) {
                if (segm.id * SEGMENT_SIZE + i < sendersCur) return
                cell@while (true) {
                    val state = segm.getState(i)
                    when {
                        state === null || state === SHOULD_BUFFER -> {
                            if (segm.casState(i, state, CHANNEL_CLOSED)) break@cell
                        }
                        state is WaiterEB -> {
                            if (segm.casState(i, state, CHANNEL_CLOSED)) {
                                if (state.waiter.closeReceiver()) expandBuffer()
                                break@cell
                            }
                        }
                        state is Waiter -> {
                            if (segm.casState(i, state, CHANNEL_CLOSED)) {
                                if (state.closeReceiver()) expandBuffer()
                                break@cell
                            }
                        }
                        else -> break@cell
                    }
                }
            }
            segm = segm.prev
        }
    }

    private fun Any.closeReceiver() = closeWaiter(receiver = true)
    private fun Any.closeSender() = closeWaiter(receiver = false)

    private fun Any.closeWaiter(receiver: Boolean): Boolean {
        val cause = getCloseCause()
        return when (this) {
            is SenderBroadcast -> {
                this.cont.resume(false)
                true
            }
            is CancellableContinuation<*> -> {
                val exception = if (receiver) receiveException(cause) else sendException(cause)
                this.tryResumeWithException(exception)?.also { this.completeResume(it) }.let { it !== null }
            }
            is ReceiveCatching<*> -> {
                this.cont.tryResume(closed(cause))?.also { this.cont.completeResume(it) }.let { it !== null }
            }
            is BufferedChannel<*>.BufferedChannelIterator -> {
                receiveResult = ClosedChannel(cause)
                val cont = this.cont!!
                if (cause == null) {
                    cont.tryResume(false)?.also { cont.completeResume(it); this.cont = null }.let { it !== null }
                } else {
                    cont.tryResumeWithException(cause)?.also { cont.completeResume(it); this.cont = null }.let { it !== null }
                }
            }
            is SelectInstance<*> -> this.trySelect(this@BufferedChannel, CHANNEL_CLOSED)
            else -> error("Unexpected waiter: $this")
        }
    }


    // ######################
    // ## Iterator Support ##
    // ######################

    override fun iterator(): ChannelIterator<E> = BufferedChannelIterator()

    internal open inner class BufferedChannelIterator : ChannelIterator<E>, CancelHandler(), Waiter {
        @JvmField
        var receiveResult: Any? = NO_RECEIVE_RESULT
        @JvmField
        var cont: CancellableContinuation<Boolean>? = null

        private var segment: ChannelSegment<E>? = null
        private var i = -1
        // on cancellation
        override fun invoke(cause: Throwable?) {
            segment?.onCancellation(i)
            onReceiveDequeued()
        }

        override suspend fun hasNext(): Boolean = receiveImpl(
            waiter = null,
            onRendezvous = { element ->
                this.receiveResult = element
                onReceiveSynchronizationCompletion()
                true
            },
            onSuspend = { _, _ -> error("unreachable") },
            onClosed = { onCloseHasNext() },
            onNoWaiter = { segm, i, r -> hasNextSuspend(segm, i, r) }
        )

        private fun onCloseHasNext(): Boolean {
            val cause = getCloseCause()
            onReceiveSynchronizationCompletion()
            this.receiveResult = ClosedChannel(cause)
            if (cause == null) return false
            else throw recoverStackTrace(cause)
        }

        private suspend fun hasNextSuspend(
            segm: ChannelSegment<E>,
            i: Int,
            r: Long
        ): Boolean = suspendCancellableCoroutineReusable { cont ->
            this.cont = cont
            receiveImplOnNoWaiter(
                segm, i, r,
                waiter = this,
                onRendezvous = { element ->
                    this.receiveResult = element
                    this.cont = null
                    onReceiveSynchronizationCompletion()
                    cont.resume(true) {
                        onUndeliveredElement?.callUndeliveredElement(element, cont.context)
                    }
                },
                onSuspend = { segment, i ->
                    this.segment = segment
                    this.i = i
                    cont.invokeOnCancellation(this.asHandler)
                    onReceiveEnqueued()
                    onReceiveSynchronizationCompletion()
                },
                onClosed = {
                    this.cont = null
                    val cause = getCloseCause()
                    this.receiveResult = ClosedChannel(cause)
                    onReceiveSynchronizationCompletion()
                    if (cause == null) {
                        cont.resume(false)
                    } else {
                        cont.resumeWithException(recoverStackTrace(cause))
                    }
                }
            )
        }

        @Suppress("UNCHECKED_CAST")
        override fun next(): E {
            // Read the already received result, or [NO_RECEIVE_RESULT] if [hasNext] has not been invoked yet.
            check(receiveResult !== NO_RECEIVE_RESULT) { "`hasNext()` has not been invoked" }
            val result = receiveResult
            receiveResult = NO_RECEIVE_RESULT
            // Is this channel closed?
            if (result is ClosedChannel) throw recoverStackTrace(receiveException(result.cause))
            // Return the element.
            return result as E
        }

        fun tryResumeHasNext(element: E): Boolean {
            this.receiveResult = element
            val cont = this.cont!!
            this.cont = null
            return cont.tryResume(true, null, onUndeliveredElement?.bindCancellationFun(element, cont.context)).let {
                if (it !== null) {
                    cont.completeResume(it)
                    true
                } else false
            }
        }
    }
    private class ClosedChannel(@JvmField val cause: Throwable?)

    // #################################################
    // # isClosedFor[Send,Receive] and isEmpty SUPPORT #
    // #################################################

    @ExperimentalCoroutinesApi
    override val isClosedForSend: Boolean
        get() = sendersAndCloseStatus.value.isClosedForSend0

    private val Long.isClosedForSend0 get() =
        isClosed(this, sendersCur = this.counter, isClosedForReceive = false)

    @ExperimentalCoroutinesApi
    override val isClosedForReceive: Boolean
        get() = sendersAndCloseStatus.value.isClosedForReceive0

    private val Long.isClosedForReceive0 get() =
        isClosed(this, sendersCur = this.counter, isClosedForReceive = true)

    private fun isClosed(
        sendersAndCloseStatusCur: Long,
        sendersCur: Long,
        isClosedForReceive: Boolean
    ) = when (sendersAndCloseStatusCur.closeStatus) {
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
            completeClose(sendersCur)
            // When `isClosedForReceive` is `false`, always return `true`.
            // Otherwise, it is possible that the channel is closed but
            // still has elements to retrieve.
            if (isClosedForReceive) !hasElements() else true
        }
        // This channel has been successfully cancelled.
        // Help to complete the cancellation procedure to
        // guarantee linearizability and return `true`.
        CLOSE_STATUS_CANCELLED -> {
            completeCancel(sendersCur)
            true
        }
        else -> error("unexpected close status: ${sendersAndCloseStatusCur.closeStatus}")
    }

    @ExperimentalCoroutinesApi
    override val isEmpty: Boolean get() =
        if (sendersAndCloseStatus.value.isClosedForReceive0) false
        else if (hasElements()) false
        else !sendersAndCloseStatus.value.isClosedForReceive0

    /**
     * Checks whether this channel contains elements to retrieve.
     * Unfortunately, simply comparing the counters is not sufficient,
     * as there can be cells in INTERRUPTED state due to cancellation.
     * Therefore, this function tries to fairly find the first element,
     * updating the `receivers` counter correspondingly.
     */
    internal fun hasElements(): Boolean {
        // Read the segment before accessing `receivers` counter.
        var segm = receiveSegment.value
        while (true) {
            // Is there a chance that this channel has elements?
            val r = receivers.value
            val s = sendersAndCloseStatus.value.counter
            if (s <= r) return false // no elements
            // Try to access the `r`-th cell.
            // Get the corresponding segment first.
            val id = r / SEGMENT_SIZE
            if (segm.id != id) {
                // Find the required segment, and retry the operation when
                // the segment with the specified id has not been found
                // due to be full of cancelled cells. Also, when the segment
                // has not been found and the channel is already closed,
                // complete with `false`.
                segm = findSegmentHasElements(id, segm).let {
                    if (it.isClosed) return false
                    if (it.segment.id != id) {
                        updateReceiversIfLower(it.segment.id * SEGMENT_SIZE)
                        null
                    } else it.segment
                } ?: continue
            }
            // Does the `r`-th cell contain waiting sender or buffered element?
            val i = (r % SEGMENT_SIZE).toInt()
            if (!isCellEmpty(segm, i, r)) return true
            // The cell is empty. Update `receivers` counter and try again.
            receivers.compareAndSet(r, r + 1)
        }
    }

    /**
     * Checks whether this cell contains a buffered element
     * or a waiting sender, returning `false` in this case.
     * Otherwise, if this cell is empty (due to waiter cancellation,
     * channel closing, or marking it as `BROKEN`), the operation
     * returns `true`.
     */
    private fun isCellEmpty(
        segm: ChannelSegment<E>,
        i: Int, // the cell index in `segm`
        r: Long // the global cell index
    ): Boolean {
        // The logic is similar to `updateCellReceive` with the only difference
        // that this operation does not change the state and retrieve the element.
        // TODO: simplify the conditions and document them.
        while (true) {
            val state = segm.getState(i)
            when {
                state === null || state === SHOULD_BUFFER -> {
                    if (segm.casState(i, state, BROKEN)) {
                        expandBuffer()
                        return true
                    }
                }
                state === BUFFERED -> {
                    return false
                }
                state === INTERRUPTED -> {
                    if (segm.casState(i, state, INTERRUPTED_R)) return true
                }
                state === INTERRUPTED_EB -> return true
                state === INTERRUPTED_R -> return true
                state === CHANNEL_CLOSED -> return true
                state === DONE -> return true
                state === BROKEN -> return true
                state === RESUMING_EB || state === RESUMING_R_EB -> continue // spin-wait
                else -> return receivers.value != r
            }
        }
    }

    // #######################
    // # SEGMENTS MANAGEMENT #
    // #######################

    private fun findSegmentSend(id: Long, start: ChannelSegment<E>) =
        sendSegment.findSegmentAndMoveForward(id, start, ::createSegment).let {
            if (it.isClosed) {
                completeCloseOrCancel()
                null
            } else {
                val segm = it.segment
                if (segm.id != id) {
                    assert { segm.id > id }
                    updateSendersIfLower(segm.id * SEGMENT_SIZE)
                    null
                } else segm
            }
        }

    private fun updateSendersIfLower(value: Long): Unit =
        sendersAndCloseStatus.loop { cur ->
            val curCounter = cur.counter
            if (curCounter >= value) return
            val update = constructSendersAndCloseStatus(curCounter, cur.closeStatus)
            if (sendersAndCloseStatus.compareAndSet(cur, update)) return
        }

    private fun updateReceiversIfLower(value: Long): Unit =
        receivers.loop { cur ->
            if (cur >= value) return
            if (receivers.compareAndSet(cur, value)) return
        }

    private fun findSegmentReceive(id: Long, start: ChannelSegment<E>): SegmentOrClosed<ChannelSegment<E>> =
        receiveSegment.findSegmentAndMoveForward(id, start, ::createSegment).also {
            if (it.isClosed) {
                completeCloseOrCancel()
            } else {
                if (it.segment.id != id)
                    updateReceiversIfLower(it.segment.id * SEGMENT_SIZE)
            }
        }

    private fun findSegmentHasElements(id: Long, start: ChannelSegment<E>) =
        receiveSegment.findSegmentAndMoveForward(id, start, ::createSegment)

    private fun findSegmentBuffer(id: Long, start: ChannelSegment<E>) =
        bufferEndSegment.findSegmentAndMoveForward(id, start, ::createSegment)

    // ##################
    // # FOR DEBUG INFO #
    // ##################

    internal val receiversCounter: Long get() = receivers.value
    internal val sendersCounter: Long get() = sendersAndCloseStatus.value.counter

    // Returns a debug representation of this channel,
    // which we actively use in Lincheck tests.
    override fun toString(): String {
        val data = arrayListOf<String>()
        val head = if (receiveSegment.value.id < sendSegment.value.id) receiveSegment.value else sendSegment.value
        var cur = head
        while (true) {
            repeat(SEGMENT_SIZE) { i ->
                val w = cur.getState(i)
                val e = cur.getElement(i)
                val wString = when (w) {
                    is CancellableContinuation<*> -> "cont"
                    is SelectInstance<*> -> "select"
                    is ReceiveCatching<*> -> "receiveCatching"
                    is SenderBroadcast -> "send(broadcast)"
                    else -> w.toString()
                }
                val eString = e.toString()
                data += "($wString,$eString)"
            }
            cur = cur.next ?: break
        }
        var dataStartIndex = head.id * SEGMENT_SIZE
        while (data.isNotEmpty() && data.first() == "(null,null)") {
            data.removeFirst()
            dataStartIndex++
        }
        while (data.isNotEmpty() && data.last() == "(null,null)") data.removeLast()
        return "S=${sendersAndCloseStatus.value.counter},R=${receivers.value},B=${bufferEnd.value}," +
               "C=${sendersAndCloseStatus.value.closeStatus},data=${data},dataStartIndex=$dataStartIndex," +
               "S_SegmId=${sendSegment.value.id},R_SegmId=${receiveSegment.value.id},B_SegmId=${bufferEndSegment.value?.id}"
    }
}

/**
 * The channel is represented as a list of segments, which simulates an infinite array.
 * Each segment has its own [id], which increase from the beginning. These [id]s help
 * to update [BufferedChannel.sendSegment], [BufferedChannel.receiveSegment],
 * and [BufferedChannel.bufferEndSegment] correctly.
 */
internal class ChannelSegment<E>(id: Long, prev: ChannelSegment<E>?, pointers: Int) : Segment<ChannelSegment<E>>(id, prev, pointers) {
    private val data = atomicArrayOfNulls<Any?>(SEGMENT_SIZE * 2) // 2 registers per slot: state + element
    override val numberOfSlots: Int get() = SEGMENT_SIZE

    // ##########################################
    // # Manipulation with the Element Register #
    // ##########################################

    inline fun storeElement(index: Int, element: E) {
        setElementLazy(index, element)
    }

    inline fun getElement(index: Int) = data[index * 2].value as E

    inline fun retrieveElement(index: Int): E = getElement(index).also { cleanElement(index) }

    inline fun cleanElement(index: Int) {
        setElementLazy(index, null)
    }

    private inline fun setElementLazy(index: Int, value: Any?) {
        data[index * 2].lazySet(value)
    }

    // ########################################
    // # Manipulation with the State Register #
    // ########################################

    inline fun getState(index: Int): Any? = data[index * 2 + 1].value

    inline fun setState(index: Int, value: Any?) {
        data[index * 2 + 1].value = value
    }

    inline fun setStateLazy(index: Int, value: Any?) {
        data[index * 2 + 1].lazySet(value)
    }

    inline fun casState(index: Int, from: Any?, to: Any?) = data[index * 2 + 1].compareAndSet(from, to)

    inline fun getAndSetState(index: Int, value: Any?) = data[index * 2 + 1].getAndSet(value)

    // ########################
    // # Cancellation Support #
    // ########################

    fun onCancellation(index: Int, onUndeliveredElement: OnUndeliveredElement<E>? = null, context: CoroutineContext? = null) {
        // Update the cell state first.
        data[index * 2 + 1].update {
            // Is this cell already processed?
            if (it !is Waiter) return
            // Replace the stored waiter with the INTERRUPTED state.
            INTERRUPTED
        }
        // Call `onUndeliveredElement` if required.
        onUndeliveredElement?.callUndeliveredElement(getElement(index), context!!)
        // Clean the element slot.
        cleanElement(index)
        // Inform the segment that one more slot has been cleaned.
        onSlotCleaned()
    }
}
private fun <E> createSegment(id: Long, prev: ChannelSegment<E>?) = ChannelSegment(id, prev, 0)
@SharedImmutable
private val NULL_SEGMENT = createSegment<Any?>(-1, null)
/**
 * Number of cells in each segment.
 */
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.bufferedChannel.segmentSize", 32)

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
  When the channel is rendezvouze or unlimited, the `bufferEnd` counter
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
  Cell states. The initial "empty" state is represented
  with `null`, and waiting operations are represented with
  [Waiter] instances. Please see the [BufferedChannel]
  documentation for more details.
 */
@SharedImmutable // The cell stores a buffered element.
private val BUFFERED = Symbol("BUFFERED")
// Concurrent `expandBuffer(..)` can inform the
// upcoming sender that it should buffer the element.
@SharedImmutable
private val SHOULD_BUFFER = Symbol("SHOULD_BUFFER")
// Indicates that a receiver (R suffix) is resuming
// the suspended sender; after that, it should update
// the state to either `DONE` (on success) or
// `INTERRUPTED_R` (on failure).
@SharedImmutable
private val RESUMING_R = Symbol("RESUMING_R")
// Indicates that `expandBuffer(..)` is resuming the
// suspended sender; after that, it should update the
// state to either `BUFFERED` (on success) or
// `INTERRUPTED_EB` (on failure).
@SharedImmutable
private val RESUMING_EB = Symbol("RESUMING_EB")
// TODO
@SharedImmutable
private val RESUMING_R_EB = Symbol("RESUMING_R_EB")
@SharedImmutable
private val BROKEN = Symbol("BROKEN")
// When the element is successfully transferred (possibly,
// through buffering), the cell moves to `DONE` state.
@SharedImmutable
private val DONE = Symbol("DONE")
// When the waiter is cancelled, it moves the cell to
// `INTERRUPTED` state; thus, informing other parties
// that may come to the cell and avoiding memory leaks.
@SharedImmutable
private val INTERRUPTED = Symbol("INTERRUPTED")
// TODO
@SharedImmutable
private val INTERRUPTED_R = Symbol("INTERRUPTED_R")
// When the cell is already covered by both sender and
// receiver (`sender` and `receivers` counters are greater
// than the cell number), the `expandBuffer(..)` procedure
// cannot distinguish which kind of operation is stored
// in the cell. Thus, it wraps the waiter with this descriptor,
// informing the possibly upcoming receiver that it should
// complete the `expandBuffer(..)` procedure if the waiter
// stored in the cell is sender. In turn, senders ignore this
// information.
private class WaiterEB(@JvmField val waiter: Any) {
    override fun toString() = "ExpandBufferDesc($waiter)"
}
// Similarly to the situation described for [WaiterEB],
// the `expandBuffer(..)` procedure cannot distinguish
// whether sender or receiver was stored in the cell when
// its state is `INTERRUPTED`. Thus, it updates the state
// to `INTERRUPTED_EB`, informing the possibly upcoming
// receiver that it should complete the `expandBuffer(..)`
// procedure if the cancelled waiter stored in the cell
// was sender.
@SharedImmutable
private val INTERRUPTED_EB = Symbol("INTERRUPTED_EB")
// Indicates that the channel is already closed,
// and no more operation should not touch this cell.
@SharedImmutable
internal val CHANNEL_CLOSED = Symbol("CHANNEL_CLOSED")


/**
 * To distinguish suspended [BufferedChannel.receive] and
 * [BufferedChannel.receiveCatching] operation, the last
 * is wrapped with this class.
 */
private class ReceiveCatching<E>(
    @JvmField val cont: CancellableContinuation<ChannelResult<E>>
) : Waiter

/*
  Internal results for [BufferedChannel.updateCellReceive].
  On successful rendezvous with waiting sender or
  buffered element retrieval, the corresponding element
  is returned as result of [BufferedChannel.updateCellReceive].
 */
@SharedImmutable
private val SUSPEND = Symbol("SUSPEND")
@SharedImmutable
private val NO_WAITER = Symbol("NO_WAITER")
@SharedImmutable
private val FAILED = Symbol("FAILED")

/*
  Internal results for [BufferedChannel.updateCellSend]
 */
private const val RESULT_RENDEZVOUS = 0
private const val RESULT_BUFFERED = 1
private const val RESULT_SUSPEND = 2
private const val RESULT_NO_WAITER = 3
private const val RESULT_FAILED = 4

/**
 * Special value for [BufferedChannel.BufferedChannelIterator.receiveResult]
 * that indicates the absence of pre-received result.
 */
@SharedImmutable
private val NO_RECEIVE_RESULT = Symbol("NO_RECEIVE_RESULT")


/*
  The channel closing statuses. The transition scheme is the following:
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
  The `senders` counter and the channel closing status
  are stored in a single 64-bit register to save the space
  and reduce the number of reads in sending operations.
  The code below encapsulates the required bit arithmetics.
 */
private const val CLOSE_STATUS_SHIFT = 60
private const val COUNTER_MASK = (1L shl CLOSE_STATUS_SHIFT) - 1
private inline val Long.counter get() = this and COUNTER_MASK
private inline val Long.closeStatus: Int get() = (this shr CLOSE_STATUS_SHIFT).toInt()
private inline fun constructSendersAndCloseStatus(counter: Long, closeStatus: Int): Long =
    (closeStatus.toLong() shl CLOSE_STATUS_SHIFT) + counter

/*
  As [BufferedChannel.invokeOnClose] can be invoked concurrently
  with channel closing, we have to synchronize them. These two
  markers help with the synchronization. The resulting
  [BufferedChannel.closeHandler] state diagram is presented below:

    +------+ install handler +---------+  close  +---------+
    | null |---------------->| handler |-------->| INVOKED |
    +------+                 +---------+         +---------+
       |             +--------+
       +------------>| CLOSED |
           close     +--------+
 */
@SharedImmutable
private val CLOSE_HANDLER_CLOSED = Symbol("CLOSE_HANDLER_CLOSED")
@SharedImmutable
private val CLOSE_HANDLER_INVOKED = Symbol("CLOSE_HANDLER_INVOKED")

/**
 * Specifies the absence of closing cause, stored in [BufferedChannel.closeCause].
 * When the channel is closed or cancelled without exception, this [NO_CLOSE_CAUSE]
 * marker should be replaced with `null`.
 */
@SharedImmutable
private val NO_CLOSE_CAUSE = Symbol("NO_CLOSE_CAUSE")

/**
 * All waiters, such as [CancellableContinuationImpl], [SelectInstance], and
 * [BufferedChannel.BufferedChannelIterator], should be marked with this interface
 * to make the code faster and easier to read.
 */
@InternalCoroutinesApi
public interface Waiter