package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.ChannelResult.Companion.closed
import kotlinx.coroutines.channels.ChannelResult.Companion.failure
import kotlinx.coroutines.channels.ChannelResult.Companion.success
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.jvm.*


public open class BufferedChannel<E>(capacity: Int) : Channel<E> {
    init {
        require(capacity >= 0) { "Invalid channel capacity: $capacity, should be >=0" }
    }

    private val unlimited = capacity == Channel.UNLIMITED
    private val rendezvous = capacity == Channel.RENDEZVOUS

    // ##################################
    // ## Indices and Segment Pointers ##
    // ##################################

    private val senders = atomic(0L)
    private val receivers = atomic(0L)
    private val bufferEnd = atomic(capacity.toLong())

    private val sendSegment: AtomicRef<ChannelSegment<E>>
    private val receiveSegment: AtomicRef<ChannelSegment<E>>
    private val bufferEndSegment: AtomicRef<ChannelSegment<E>>

    private val closeStatus = atomic(0) // 1 -- CLOSED, 2 -- CANCELLED

    init {
        val s = ChannelSegment<E>(0, null, 3)
        sendSegment = atomic(s)
        receiveSegment = atomic(s)
        bufferEndSegment = atomic(s)
    }

    // For debug info
    internal val receiversCounter: Long get() = receivers.value
    internal val sendersCounter: Long get() = senders.value

    // ######################
    // ## Send and Receive ##
    // ######################

    protected open fun onReceiveEnqueued() {}
    protected open fun onReceiveDequeued() {}

    override fun trySend(element: E): ChannelResult<Unit> {
        val possible = unlimited || senders.value.let { it < receivers.value || !rendezvous && it < bufferEnd.value }
        if (!possible && closeStatus.value == 0) return failure()
        sendImpl(
            element = element,
            startSegment = this.sendSegment.value,
            waiter = INTERRUPTED,
            onRendezvous = { return success(Unit) },
            onSuspend = { _, _ -> return failure() },
            onClosed = { exception -> return closed(exception) },
            onNoWaiter = { _, _, _, _ -> error("unexpected") }
        )
        error("unexpected")
    }

    public override suspend fun send(element: E): Unit =
        sendImpl(
            element = element,
            startSegment = sendSegment.value,
            waiter = null,
            onRendezvous = {},
            onSuspend = { _, _ -> error("unexpected") },
            onClosed = { e -> throw e },
            onNoWaiter = { segm, i, elem, s -> sendSuspend(segm, i, elem, s) }
        )

    private inline fun <W> sendImpl(
        element: E,
        startSegment: ChannelSegment<E>,
        waiter: W,
        onRendezvous: () -> Unit,
        onSuspend: (segm: ChannelSegment<E>, i: Int) -> Unit,
        onClosed: (sendException: Throwable) -> Unit,
        onNoWaiter: (
            segm: ChannelSegment<E>,
            i: Int,
            element: E,
            s: Long
        ) -> Unit
    ) {
        var segm = startSegment
        while (true) {
            if (closeStatus.value > 0) {
                if (closeStatus.value == 1) completeClose() else completeCancel()
                onClosed(sendException)
                return
            }
            val s = senders.getAndIncrement()
            val id = s / SEGMENT_SIZE
            val i = (s % SEGMENT_SIZE).toInt()
            if (segm.id != id) {
                segm = findSegmentSend(id, segm).let {
                    if (it.isClosed) {
                        if (closeStatus.value == 1) completeClose() else completeCancel()
                        onClosed(sendException)
                        return
                    } else it.segment
                }
            }
            if (segm.id != id) {
                senders.compareAndSet(s + 1, segm.id * SEGMENT_SIZE)
                continue
            }
            val result = updateCellSend(segm, i, element, s, waiter)
            when {
                result === RENDEZVOUS -> {
                    onRendezvous()
                    return
                }
                result === SUSPEND -> {
                    onSuspend(segm, i)
                    return
                }
                result === FAILED -> continue
                result === NO_WAITER -> {
                    return onNoWaiter(segm, i, element, s)
                }
            }
        }
    }

    private suspend fun sendSuspend(
        segm: ChannelSegment<E>,
        i: Int,
        element: E,
        s: Long
    ) = suspendCancellableCoroutineReusable<Unit> sc@{ cont ->
        val result = updateCellSend(segm, i, element, s, cont)
        when {
            result === RENDEZVOUS -> {
                cont.resume(Unit)
            }
            result === SUSPEND -> {
                cont.invokeOnCancellation { segm.onCancellation(i) }
            }
            result === FAILED -> {
                sendImpl(
                    element = element,
                    startSegment = segm,
                    waiter = cont,
                    onRendezvous = { cont.resume(Unit) },
                    onSuspend = { segm, i -> cont.invokeOnCancellation { segm.onCancellation(i) } },
                    onClosed = { e -> cont.resumeWithException(e) },
                    onNoWaiter = { _, _, _, _ -> error("Waiter is not empty") })
            }
        }
    }

    private fun <W> updateCellSend(
        segm: ChannelSegment<E>,
        i: Int,
        element: E,
        s: Long,
        waiter: W,
    ): Any {
        segm.storeElement(i, element)
        while (true) {
            val state = segm.getState(i)
            when {
                state === null -> {
                    val rendezvous = unlimited || s < bufferEnd.value || s < receivers.value
                    if (rendezvous) {
                        if (segm.casState(i, null, BUFFERED)) return RENDEZVOUS
                    } else {
                        if (waiter === null) return NO_WAITER
                        if (segm.casState(i, null, waiter)) return SUSPEND
                    }
                }
                state === BUFFERING -> {
                    if (segm.casState(i, state, BUFFERED)) return RENDEZVOUS
                }
                state === BROKEN || state === INTERRUPTED || state === INTERRUPTED_EB || state === CLOSED -> {
                    segm.setElementLazy(i, null)
                    return FAILED
                }
                else -> {
                    segm.setState(i, DONE) // we can safely avoid CAS here
                    segm.setElementLazy(i, null)
                    val receiver = if (state is WaiterEB) state.waiter else state
                    return if (receiver.tryResumeReceiver(element)) RENDEZVOUS else FAILED
                }
            }
        }
    }

    private fun Any.tryResumeReceiver(element: E): Boolean = when {
        this is NewSelectInstance<*> -> {
            this.trySelect(this@BufferedChannel, element)
        }
        this is CancellableContinuation<*> -> {
            this as CancellableContinuation<Any?>
            tryResume(element).let {
                if (it !== null) {
                    completeResume(it)
                    true
                } else false
            }
        }
        else -> error("Unexpected waiter: $this")
    }

    private fun findSegmentSend(id: Long, start: ChannelSegment<E>) =
        sendSegment.findSegmentAndMoveForward(id, start, ::createSegment)


    override suspend fun receive(): E {
        return receiveImpl(
            startSegment = receiveSegment.value,
            waiter = null,
            onRendezvous = { e -> return e },
            onSuspend = { _, _ -> error("unexpected") },
            onClosed = { e -> throw e },
            onNoWaiter = { segm, i, r -> receiveSuspend(segm, i, r) }
        ) as E
    }

    override fun tryReceive(): ChannelResult<E> {
        if (receivers.value >= senders.value && closeStatus.value == 0) return failure()
        receiveImpl(
            startSegment = receiveSegment.value,
            waiter = INTERRUPTED,
            onRendezvous = { element -> return success(element) },
            onSuspend = { _, _ -> return failure() },
            onClosed = { exception -> return closed(exception)},
            onNoWaiter = {_, _, _ -> error("unexpected") }
        )
        error("unreachable")
    }

    private inline fun receiveImpl(
        startSegment: ChannelSegment<E>,
        waiter: Any?,
        onRendezvous: (element: E) -> Unit,
        onSuspend: (segm: ChannelSegment<E>, i: Int) -> Unit,
        onClosed: (sendException: Throwable) -> Unit,
        onNoWaiter: (
            segm: ChannelSegment<E>,
            i: Int,
            r: Long
        ) -> E
    ): Any? {
        var segm = startSegment
        while (true) {
            if (closeStatus.value == 2) {
                completeCancel()
                onClosed(this.receiveException)
                return CLOSED
            }
            val r = this.receivers.getAndIncrement()
            val id = r / SEGMENT_SIZE
            val i = (r % SEGMENT_SIZE).toInt()
            if (segm.id != id) {
                segm = findSegmentReceive(id, segm).let {
                    if (it.isClosed) {
                        if (closeStatus.value == 1) completeClose() else completeCancel()
                        onClosed(this.receiveException)
                        return CLOSED
                    } else it.segment
                }
            }
            if (segm.id != id) {
                receivers.compareAndSet(r + 1, segm.id * SEGMENT_SIZE)
                continue
            }
            val result = updateCellReceive(segm, i, r, waiter)
            when {
                result === SUSPEND -> {
                    onSuspend(segm, i)
                    return SUSPEND
                }
                result === FAILED -> continue
                result !== NO_WAITER -> { // element
                    result as E
                    onRendezvous(result)
                    return result
                }
                result === NO_WAITER -> {
                    return onNoWaiter(segm, i, r)
                }
            }
        }
    }

    private suspend fun receiveSuspend(
        segm: ChannelSegment<E>,
        i: Int,
        r: Long
    ) = suspendCancellableCoroutineReusable<E> { cont ->
        val result = updateCellReceive(segm, i, r, cont)
        when {
            result === SUSPEND -> {
                cont.invokeOnCancellation { segm.onCancellation(i) }
            }
            result === FAILED -> {
                receiveImpl(
                    startSegment = receiveSegment.value,
                    waiter = cont,
                    onRendezvous = { element -> cont.resume(element) },
                    onSuspend = { segm, i -> cont.invokeOnCancellation { segm.onCancellation(i) } },
                    onClosed = { e -> cont.resumeWithException(receiveException) },
                    onNoWaiter = { _, _, _ -> error("unexpected") }
                )
            }
            else -> {
                cont.resume(result as E)
            }
        }
    }

    private fun updateCellReceive(
        segm: ChannelSegment<E>,
        i: Int,
        r: Long,
        waiter: Any?,
    ): Any? {
        while (true) {
            val state = segm.getState(i)
            when {
                state === null || state === BUFFERING -> {
                    if (r < senders.value) {
                        if (segm.casState(i, state, BROKEN)) {
                            expandBuffer()
                            return FAILED
                        }
                    } else {
                        if (waiter === null) return NO_WAITER
                        if (segm.casState(i, state, waiter)) {
                            expandBuffer()
                            return SUSPEND
                        }
                    }
                }
                state === BUFFERED -> {
                    val element = segm.retrieveElement(i)
                    if (segm.getState(i) === BUFFERED) {
                        expandBuffer()
                        return element
                    }
                }
                state === INTERRUPTED -> {
                    if (segm.casState(i, state, INTERRUPTED_R)) return FAILED
                }
                state === INTERRUPTED_EB -> {
                    expandBuffer()
                    return FAILED
                }
                state === INTERRUPTED_R -> return FAILED
                state === BROKEN -> return FAILED
                state === CLOSED -> return FAILED
                state === RESUMING_EB -> continue // spin-wait
                else -> {
                    if (segm.casState(i, state, RESUMING_R)) {
                        val helpExpandBuffer = state is WaiterEB
                        val sender = if (state is WaiterEB) state.waiter else state
                        if (sender.tryResumeSender()) {
                            segm.setState(i, DONE)
                            expandBuffer()
                            return segm.retrieveElement(i)
                        } else {
                            if (!segm.casState(i, RESUMING_R, INTERRUPTED_R) || helpExpandBuffer)
                                expandBuffer()
                            return FAILED
                        }
                    }
                }
            }
        }
    }

    private fun Any.tryResumeSender(): Boolean = when {
        this is NewSelectInstance<*> -> {
            this.trySelect(this@BufferedChannel, Unit)
        }
        this is CancellableContinuation<*> -> {
            this as CancellableContinuation<Unit>
            tryResume(Unit).let {
                if (it !== null) {
                    completeResume(it)
                    true
                } else false
            }
        }
        else -> error("Unexpected waiter: $this")
    }

    private fun findSegmentReceive(id: Long, start: ChannelSegment<E>) =
        receiveSegment.findSegmentAndMoveForward(id, start, ::createSegment)


    private fun expandBuffer() {
        if (rendezvous || unlimited) return
        var segm = bufferEndSegment.value
        try_again@ while (true) {
            val b = bufferEnd.getAndIncrement()
            val s = senders.value
            if (s <= b) return
            val id = b / SEGMENT_SIZE
            val i = (b % SEGMENT_SIZE).toInt()
            if (segm.id != id) {
                segm = findSegmentBuffer(id, segm).let {
                    if (it.isClosed) return else it.segment
                }
            }
            if (segm.id != id) {
                bufferEnd.compareAndSet(b + 1, segm.id * SEGMENT_SIZE)
                continue@try_again
            }
            if (updateCellExpandBuffer(segm, i, b)) return
        }
    }

    private fun updateCellExpandBuffer(
        segm: ChannelSegment<E>,
        i: Int,
        b: Long
    ): Boolean {
        while (true) {
            val state = segm.getState(i)
            when {
                state === null -> {
                    if (segm.casState(i, segm, BUFFERING)) return true
                }
                state === BUFFERED || state === BROKEN || state === DONE || state == CLOSED -> return true
                state === RESUMING_R -> if (segm.casState(i, state, RESUMING_R_EB)) return true
                state === INTERRUPTED -> {
                    if (b >= receivers.value) return false
                    if (segm.casState(i, state, INTERRUPTED_EB)) return true
                }
                state === INTERRUPTED_R -> return false
                else -> {
                    if (b < receivers.value) {
                        if (segm.casState(i, state, WaiterEB(waiter = state))) return true
                    } else {
                        if (segm.casState(i, state, RESUMING_EB)) {
                            return if (state.tryResumeSender()) {
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

    private fun findSegmentBuffer(id: Long, start: ChannelSegment<E>) =
        bufferEndSegment.findSegmentAndMoveForward(id, start, ::createSegment)


    // #######################
    // ## Select Expression ##
    // #######################

    public val onSendNew: NewSelectClause2<E, BufferedChannel<E>>
        get() = NewSelectClause2Impl(
            objForSelect = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForSend as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectSend as ProcessResultFunction
        )

    public val onReceiveNew: NewSelectClause1<E>
        get() = NewSelectClause1Impl(
            objForSelect = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectReceive as ProcessResultFunction
        )

    private fun registerSelectForSend(select: NewSelectInstance<*>, element: Any?) =
        sendImpl(
            element = element as E,
            startSegment = sendSegment.value,
            waiter = select,
            onRendezvous = { select.selectInRegPhase(Unit) },
            onSuspend = { segm, i -> select.invokeOnCompletion { segm.onCancellation(i) } },
            onClosed = { select.selectInRegPhase(CLOSED) },
            onNoWaiter = { _, _, _, _ -> error("unexpected") }
        )

    private fun registerSelectForReceive(select: NewSelectInstance<*>, ignoredParam: Any?): Unit {
        receiveImpl(
            startSegment = receiveSegment.value,
            waiter = select,
            onRendezvous = { elem -> select.selectInRegPhase(elem) },
            onSuspend = { segm, i -> select.invokeOnCompletion { segm.onCancellation(i) } },
            onClosed = { select.selectInRegPhase(CLOSED) },
            onNoWaiter = { _, _, _ -> error("unexpected") }
        )
    }


    private fun processResultSelectSend(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CLOSED) throw sendException
        else this

    private fun processResultSelectReceive(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CLOSED) throw receiveException
        else selectResult

    private fun processResultSelectReceiveOrNull(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CLOSED) {
            if (closeCause.value !== null) throw receiveException
            null
        } else selectResult


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

    private val receiveException: Throwable
        get() = (closeCause.value as Throwable?) ?: ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)
    private val sendException: Throwable
        get() = (closeCause.value as Throwable?) ?: ClosedSendChannelException(DEFAULT_CLOSE_MESSAGE)

    // Stores the close handler.
    private val closeHandler = atomic<Any?>(null)

    private fun markClosed() {
        closeStatus.update {
            when (it) {
                -1 -> 2
                0 -> 1
                else -> it
            }
        }
    }

    private fun markCancelled() {
        closeStatus.value = 2
    }

    public override fun close(cause: Throwable?): Boolean = closeImpl(cause, false)

    private fun closeImpl(cause: Throwable?, cancel: Boolean): Boolean {
        if (cancel) {
            closeStatus.compareAndSet(0, -1)
        }
        val closedByThisOperation = closeCause.compareAndSet(NO_CLOSE_CAUSE, cause)
        if (cancel) markCancelled() else markClosed()
        completeClose()
        return if (closedByThisOperation) {
            // onClosed() TODO
            invokeCloseHandler()
            true
        } else false
    }

    private fun completeClose() {
        val segm = closeQueue()
        removeWaitingRequests(segm)
    }

    private fun completeCancel() {
        completeClose()
        removeRemainingBufferedElements()
    }

    private fun closeQueue(): ChannelSegment<E> {
        var segm = bufferEndSegment.value
        sendSegment.value.let { if (it.id > segm.id) segm = it }
        return segm.close()
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

    public override fun invokeOnClose(handler: (cause: Throwable?) -> Unit) {
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

    final override fun cancel(cause: Throwable?): Boolean = cancelImpl(cause)
    final override fun cancel() { cancelImpl(null) }
    final override fun cancel(cause: CancellationException?) { cancelImpl(cause) }

    private fun cancelImpl(cause: Throwable?): Boolean {
        val closedByThisOperation = closeImpl(cause, true)
        removeRemainingBufferedElements()
        return closedByThisOperation
    }

    private fun removeRemainingBufferedElements() {
        var segm: ChannelSegment<E> = sendSegment.value
        while (true) {
            segm = segm.next ?: break
        }
        var c = (segm.id + 1) * SEGMENT_SIZE - 1
        while (true) {
            for (i in SEGMENT_SIZE - 1 downTo 0) {
                while (true) {
                    val state = segm.getState(i)
                    if (receivers.value > c) return
                    when {
                        state === BUFFERED || state === BUFFERING || state === null -> if (segm.casState(i, state, CLOSED)) {
                            segm.onCancellation(i)
                            break
                        }
                        state is WaiterEB -> {
                            if (segm.casState(i, state, CLOSED)) {
                                state.waiter.closeReceiver()
                                break
                            }
                        }
                        state is CancellableContinuation<*> || state is NewSelectInstance<*> -> {
                            if (segm.casState(i, state, CLOSED)) {
                                state.closeReceiver()
                                break
                            }
                        }
                        else -> break
                    }
                }
                c--
            }
            segm = segm.prev ?: break
        }
    }

    private fun removeWaitingRequests(lastSegment: ChannelSegment<E>) {
        var segm: ChannelSegment<E>? = lastSegment
        var c = (lastSegment.id + 1) * SEGMENT_SIZE - 1
        while (segm != null) {
            for (i in SEGMENT_SIZE - 1 downTo 0) {
                while (true) {
                    val state = segm.getState(i)
                    if (c < senders.value) break
                    when {
                        state === null || state === BUFFERING -> {
                            if (segm.casState(i, state, CLOSED)) break
                        }
                        state is WaiterEB -> {
                            if (segm.casState(i, state, CLOSED)) {
                                if (state.waiter.closeSender()) expandBuffer()
                                break
                            }
                        }
                        state is CancellableContinuation<*> || state is NewSelectInstance<*> -> {
                            if (segm.casState(i, state, CLOSED)) {
                                if (state.closeSender()) expandBuffer()
                                break
                            }
                        }
                        else -> break
                    }
                }
                c--
            }
            segm = segm.prev
        }
    }

    private fun Any.closeReceiver() = closeWaiter(receiveException)
    private fun Any.closeSender() = closeWaiter(sendException)

    private fun Any.closeWaiter(exception: Throwable): Boolean =
        when (this) {
            is CancellableContinuation<*> -> {
                this.tryResumeWithException(exception)?.also { this.completeResume(it) }.let { it !== null }
            }
            is NewSelectInstance<*> -> this.trySelect(this@BufferedChannel, CLOSED)
            else -> error("Unexpected waiter: $this")
        }


    // ######################
    // ## Iterator Support ##
    // ######################

    // TODO make it extension function after `receiveOrClosed` is added.
    public override fun iterator(): ChannelIterator<E> = object : ChannelIterator<E> {
        private var result: Any? = NO_RESULT // NO_RESULT | E (next element) | CLOSED
        override suspend fun hasNext(): Boolean {
            if (result != NO_RESULT) return checkNotClosed(result)
            // Try to receive an element. Store the result even if
            // receiving fails in order to process further [hasNext]
            // and [next] invocations properly.
            result = receive() // todo: tail call optimization?
            return if (result == CLOSED) {
                if (closeCause.value == null) {
                    false
                } else {
                    throw (closeCause.value as Throwable)
                }
            } else true
        }

        private fun checkNotClosed(result: Any?): Boolean {
            return if (result === CLOSED) {
                if (closeCause.value != null) throw (closeCause.value as Throwable)
                false
            } else true
        }

        @Suppress("UNCHECKED_CAST")
        override fun next(): E =
            // Read the already received result or NO_RESULT if [hasNext] has not been invoked yet.
            when (val result = this.result) {
                // Rare case -- [hasNext] has not been invoked, invoke [receive] directly.
                NO_RESULT -> error("[hasNext] has not been invoked")
                // Channel is closed, throw the cause exception.
                CLOSED -> throw receiveException
                // An element has been received successfully.
                else -> {
                    // Reset the [result] field and return the element.
                    this.result = NO_RESULT
                    result as E
                }
            }
    }

    override fun toString(): String {
        val data = arrayListOf<String>()
        val head = if (receiveSegment.value.id < sendSegment.value.id) receiveSegment.value else sendSegment.value
        var cur = head
        while (true) {
            repeat(SEGMENT_SIZE) { i ->
                val w = cur.getState(i)
                val e = cur.getElement(i)
                val wString = when {
                    w is CancellableContinuation<*> -> "cont"
                    else -> w.toString()
                }
                val eString = e.toString()
                data += "($wString,$eString)"
            }
            cur = cur.next ?: break
        }
        var dataStart = head.id * SEGMENT_SIZE
        while (data.isNotEmpty() && data.first() == "(null,null)") {
            data.removeFirst()
            dataStart++
        }
        while (data.isNotEmpty() && data.last() == "(null,null)") data.removeLast()
        return "S=${senders.value},R=${receivers.value},B=${bufferEnd.value},data=${data},dataStart=$dataStart"
    }

    @ExperimentalCoroutinesApi
    override val isClosedForSend: Boolean
        get() = closeStatus.value > 0

    @ExperimentalCoroutinesApi
    override val isClosedForReceive: Boolean get() {
        closeStatus.value.let {
            if (it == 0 || it == -1) return false
            if (it == 2) {
                completeCancel()
                return true
            }
        }
        // The channel is closed but not cancelled.
        // Are there elements to retrieve?
        completeClose()
        return !hasElements()
    }

    @ExperimentalCoroutinesApi
    override val isEmpty: Boolean get() {
        val hasElements = hasElements()
        closeStatus.value.let {
            if (it == 0 || it == -1) return !hasElements
            if (it == 1) completeClose() else completeCancel()
        }
        return false
    }

    private fun hasElements(): Boolean {
        var segm = receiveSegment.value
        while (true) {
            if (closeStatus.value == 2) {
                completeCancel()
                return false
            }
            val s = senders.value
            val r = receivers.value
            if (s <= r) return false
            val id = r / SEGMENT_SIZE
            val i = (r % SEGMENT_SIZE).toInt()
            if (segm.id != id) {
                segm = findSegmentReceive(id, segm).let {
                    if (it.isClosed) {
                        if (closeStatus.value == 1) completeClose() else completeCancel()
                        return false
                    } else it.segment
                }
            }
            if (segm.id != id) {
                receivers.compareAndSet(r, segm.id * SEGMENT_SIZE)
                continue
            }
            if (!isCellEmpty(segm, i, r)) return true
            receivers.compareAndSet(r, r + 1)
        }
    }

    private fun isCellEmpty(
        segm: ChannelSegment<E>,
        i: Int,
        r: Long
    ): Boolean {
        while (true) {
            val state = segm.getState(i)
            when {
                state === null || state === BUFFERING -> {
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
                state === CLOSED -> return true
                state === DONE -> return true
                state === BROKEN -> return true
                state === RESUMING_EB -> continue // spin-wait
                else -> return receivers.value != r
            }
        }
    }


    override suspend fun receiveCatching(): ChannelResult<E> {
        TODO("Not yet implemented")
    }

    override val onSend: SelectClause2<E, SendChannel<E>>
        get() = TODO("Not yet implemented")
    override val onReceive: SelectClause1<E>
        get() = TODO("Not yet implemented")
    override val onReceiveCatching: SelectClause1<ChannelResult<E>>
        get() = TODO("Not yet implemented")
}

/**
 * The channel is represented as a list of segments, which simulates an infinite array.
 * Each segment has its own [id], which increase from the beginning. These [id]s help
 * to update [BufferedChannel.head] and [BufferedChannel.tail] correctly
 */
internal class ChannelSegment<E>(id: Long, prev: ChannelSegment<E>?, pointers: Int) :
    Segment<ChannelSegment<E>>(id, prev, pointers) {
    private val data = atomicArrayOfNulls<Any?>(SEGMENT_SIZE * 2) // 2 registers per slot

    override val maxSlots: Int get() = SEGMENT_SIZE

    inline fun getElement(index: Int): Any? = data[index * 2].value
    inline fun setElementLazy(index: Int, value: Any?) {
        data[index * 2].lazySet(value)
    }

    inline fun getState(index: Int): Any? = data[index * 2 + 1].value
    inline fun setState(index: Int, value: Any?) {
        data[index * 2 + 1].value = value
    }

    inline fun casState(index: Int, from: Any?, to: Any?) = data[index * 2 + 1].compareAndSet(from, to)

    fun storeElement(i: Int, element: E) {
        val element: Any = if (element === null) NULL_ELEMENT else element
        setElementLazy(i, element)
    }

    fun retrieveElement(i: Int): E {
        val element = getElement(i)
        setElementLazy(i, null)
        return (if (element === NULL_ELEMENT) null else element) as E
    }

    fun onCancellation(i: Int) {
        data[i * 2 + 1].update {
            if (it === RESUMING_R || it === RESUMING_EB || it === RESUMING_R_EB ||
                it === INTERRUPTED || it === INTERRUPTED_R || it === INTERRUPTED_EB ||
                it === CLOSED || it is WaiterEB
            ) return
            INTERRUPTED
        }
        setElementLazy(i, null)
        onSlotCleaned()
    }
}

private fun <E> createSegment(id: Long, prev: ChannelSegment<E>?) = ChannelSegment(id, prev, 0)

private fun CancellableContinuation<*>.tryResumeReceive(element: Any?): Boolean {
    this as CancellableContinuation<Any?>
    val token = tryResume(element) ?: return false
    completeResume(token)
    return true
}

private fun CancellableContinuation<*>.tryResumeSend(): Boolean {
    this as CancellableContinuation<Unit>
    val token = tryResume(Unit) ?: return false
    completeResume(token)
    return true
}

private class WaiterEB(@JvmField val waiter: Any) {
    override fun toString() = "ExpandBufferDesc($waiter)"
}

private class ReceiveOrCatching(@JvmField val receiver: Any)

// Number of cells in each segment
private val SEGMENT_SIZE = 2 // systemProp("kotlinx.coroutines.bufferedChannel.segmentSize", 32)

// Cell states
private val BUFFERING = Symbol("BUFFERING")
private val BUFFERED = Symbol("BUFFERED")
private val RESUMING_R = Symbol("RESUMING_R")
private val RESUMING_EB = Symbol("RESUMING_EB")
private val RESUMING_R_EB = Symbol("RESUMING_R_EB")
private val BROKEN = Symbol("BROKEN")
private val DONE = Symbol("DONE")
private val INTERRUPTED = Symbol("INTERRUPTED")
private val INTERRUPTED_R = Symbol("INTERRUPTED_R")
private val INTERRUPTED_EB = Symbol("INTERRUPTED_EB")

// Special values for `CLOSE_HANDLER`
private val CLOSE_HANDLER_CLOSED = Symbol("CLOSE_HANDLER_CLOSED")
private val CLOSE_HANDLER_INVOKED = Symbol("CLOSE_HANDLER_INVOKED")

// Specifies the absence of close cause
private val NO_CLOSE_CAUSE = Symbol("NO_CLOSE_CAUSE")

// Senders should store this value when the element is null
private val NULL_ELEMENT = Symbol("NULL")

// Special return values
private val RENDEZVOUS = Symbol("RENDEZVOUS")
private val SUSPEND = Symbol("SUSPEND")
private val NO_WAITER = Symbol("NO_WAITER")
private val FAILED = Symbol("FAILED")
private val CLOSED = Symbol("CLOSED")
private val NO_RESULT = Symbol("NO_RESULT")