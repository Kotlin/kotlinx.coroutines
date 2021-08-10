package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
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

    private val closed = atomic(false)

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

    public override fun offer(element: E): Boolean {
        // Is there a chance to perform this offer?
        while (true) {
            val possible = unlimited || senders.value.let { it < receivers.value || !rendezvous && it < bufferEnd.value }
            if (!possible) return false
            trySendRendezvous(this.sendSegment.value, element, onRendezvous = { return true }) { segm, i, s ->
                if (storeSender(segm, i, element, s, waiter = OFFER,
                        onRendezvous = { return true },
                        cancellationSetup = {})
                ) return false
            }
        }
    }

    public suspend fun send2(element: E): Unit =
        trySendRendezvous(this.sendSegment.value, element, onRendezvous = {}) { segm, i, s ->
            sendSuspend(element, segm, i, s)
        }

    private inline fun trySendRendezvous(
        startSegment: ChannelSegment<E>,
        element: E,
        onRendezvous: () -> Unit,
        oRendezvousFailed: (segm: ChannelSegment<E>, i: Int, s: Long) -> Unit
    ) {
        var segm = startSegment
        while (true) {
            checkNotClosedForSend()
            val s = senders.getAndIncrement()
            val id = s / SEGMENT_SIZE
            val i = (s % SEGMENT_SIZE).toInt()
            if (segm.id != id) segm = findSegmentSend(id, segm)
            if (segm.id != id) {
                senders.compareAndSet(s + 1, segm.id * SEGMENT_SIZE)
                continue
            }
            val doNotSuspend = unlimited || s < receivers.value || (!rendezvous && s < bufferEnd.value)
            if (doNotSuspend) { // rendezvous or buffering
                segm.cleanPrev()
                if (trySendWithoutSuspension(segm = segm, i = i, element = element)) {
                    onRendezvous()
                    return
                }
            } else {
                return oRendezvousFailed(segm, i, s)
            }
        }
    }

    private fun findSegmentSend(id: Long, start: ChannelSegment<E>) =
        sendSegment.findSegmentAndMoveForward(id, start, ::createSegment).segment

    public override suspend fun send(element: E) {
        var segm = sendSegment.value
        while (true) {
            checkNotClosedForSend()
            val s = senders.getAndIncrement()
            val id = s / SEGMENT_SIZE
            val i = (s % SEGMENT_SIZE).toInt()
            if (segm.id != id) segm = findSegmentSend(id, segm)
            if (segm.id != id) {
                senders.compareAndSet(s + 1, segm.id * SEGMENT_SIZE)
                continue
            }
            val doNotSuspend = unlimited || s < receivers.value || (!rendezvous && s < bufferEnd.value)
            if (doNotSuspend) { // rendezvous or buffering
                segm.cleanPrev()
                if (trySendWithoutSuspension(segm = segm, i = i, element = element)) {
                    return
                }
            } else {
                return sendSuspend(element, segm, i, s)
            }
        }
    }

    private suspend fun sendSuspend(
        element: E,
        segm: ChannelSegment<E>,
        i: Int,
        s: Long
    ) = suspendCancellableCoroutineReusable<Unit> sc@{ cont ->
        if (storeSenderSuspend(cont, element, segm, i, s)) return@sc
        while (true) {
            trySendRendezvous(segm, element,
                onRendezvous = { cont.resume(Unit); return@sc },
                oRendezvousFailed = { segm, i, s ->
                    if (storeSenderSuspend(cont, element, segm, i, s)) { return@sc }
                }
            )
        }
    }

    private fun storeSenderSuspend(
        cont: CancellableContinuation<Unit>,
        element: E,
        segm: ChannelSegment<E>,
        i: Int,
        s: Long
    ) = storeSender(
        segm, i, element, s, waiter = cont,
        onRendezvous = { cont.resume(Unit) },
        cancellationSetup = { cont.invokeOnCancellation { segm.onCancellation(i) } }
    )

    private fun trySendWithoutSuspension(
        segm: ChannelSegment<E>,
        i: Int,
        element: E
    ): Boolean {
        while (true) {
            val state = segm.getState(i)
            when {
                state === null || state === BUFFERING -> {
                    segm.setElementLazy(i, element)
                    if (segm.casState(i, state, BUFFERED)) return true
                    segm.setElementLazy(i, null)
                }
                state === BROKEN || state === CANCELLED || state === INTERRUPTED -> return false
                state is ExpandBufferDesc -> {
                    segm.casState(i, state, state.waiter)
                }
                state is CancellableContinuation<*> -> {
                    if (segm.casState(i, state, DONE)) return state.tryResumeReceive(element).also {
                        onReceiveDequeued()
                    }
                }
                state is NewSelectInstance<*> -> {
                    if (segm.casState(i, state, DONE)) return state.trySelect(this, element).also {
                        onReceiveDequeued()
                    }
                }
                else -> error("Unexpected state: $state")
            }
        }
    }

    private inline fun <W> storeSender(
        segm: ChannelSegment<E>,
        i: Int,
        element: E,
        s: Long,
        waiter: W,
        onRendezvous: (W) -> Unit,
        cancellationSetup: (W) -> Unit
    ): Boolean {
        segm.storeElement(i, element)
        while (true) {
            val state = segm.getState(i)
            when {
                state === BROKEN -> {
                    segm.setElementLazy(i, null)
                    return false
                }
                state === BUFFERING -> if (segm.casState(i, state, BUFFERED)) {
                    onRendezvous(waiter)
                    return true
                }
                state === null -> if (segm.casState(i, state, waiter)) break
                else -> error("Unexpected state: $state")
            }
        }
        if (s < bufferEnd.value && segm.casState(i, waiter, BUFFERED)) {
            onRendezvous(waiter)
        } else {
            cancellationSetup(waiter)
        }
        return true
    }

    private fun checkNotClosedForSend() {
        if (closed.value) throw sendException
    }

    public override fun poll(): E? {
        // Is there a chance to perform this poll?
        if (receivers.value >= senders.value) return null
        var element: Any? = NULL_ELEMENT
        tryReceiveRendezvousUnit(
            onRendezvous = { e -> element = e},
            oRendezvousFailed = { segm, i ->
                storeReceiver(segm, i, waiter = CANCELLED,
                    onElimination = { w, e -> element = e },
                    cancellationSetup = {}
                )
            }
        )
        return if (element === NULL_ELEMENT) null else element as E
    }

    public suspend fun receive2(): E =
        tryReceiveRendezvous(
            onRendezvous = {},
            oRendezvousFailed = { segm, i -> receiveSuspend(segm, i) }
        )

    public override suspend fun receive(): E {
        var segm = receiveSegment.value
        while (true) {
            val r = this.receivers.getAndIncrement()
            val id = r / SEGMENT_SIZE
            val i = (r % SEGMENT_SIZE).toInt()
            if (segm.id != id) segm = findSegmentReceive(id, segm)
            if (segm.id != id) {
                receivers.compareAndSet(r + 1, segm.id * SEGMENT_SIZE)
                continue
            }
            if (r < senders.value) {
                val element = tryReceiveWithoutSuspension(segm, i)
                if (element === FAILED_RESULT) continue
                return element as E
            } else {
                return receiveSuspend(segm, i)
            }
        }
    }

    private inline fun tryReceiveRendezvousImpl(
        onRendezvous: (element: E) -> Unit,
        oRendezvousFailed: (segm: ChannelSegment<E>, i: Int) -> Any?
    ): Any? {
        while (true) {
            var segm = receiveSegment.value
            val r = this.receivers.getAndIncrement()
            val id = r / SEGMENT_SIZE
            val i = (r % SEGMENT_SIZE).toInt()
            if (segm.id != id) segm = findSegmentReceive(id, segm)
            if (segm.id != id) {
                receivers.compareAndSet(r + 1, segm.id * SEGMENT_SIZE)
                continue
            }
            if (r < senders.value) {
                val element = tryReceiveWithoutSuspension(segm, i)
                if (element === FAILED_RESULT) continue
                onRendezvous(element as E)
                return element
            } else {
                return oRendezvousFailed(segm, i)
            }
        }
    }

    private fun findSegmentReceive(id: Long, start: ChannelSegment<E>) =
        receiveSegment.findSegmentAndMoveForward(id, start, ::createSegment).segment

    private inline fun tryReceiveRendezvous(
        onRendezvous: (element: E) -> Unit,
        oRendezvousFailed: (segm: ChannelSegment<E>, i: Int) -> E
    ): E = tryReceiveRendezvousImpl(onRendezvous, oRendezvousFailed) as E

    private inline fun tryReceiveRendezvousUnit(
        onRendezvous: (element: E) -> Unit,
        oRendezvousFailed: (segm: ChannelSegment<E>, i: Int) -> Unit
    ) {
        tryReceiveRendezvousImpl(onRendezvous, oRendezvousFailed)
    }

    private fun tryReceiveWithoutSuspension(
        segm: ChannelSegment<E>,
        i: Int,
    ): Any? {
        while (true) {
            val state = segm.getState(i)
            when {
                state === BUFFERED -> {
                    val element = segm.retrieveElement(i)
                    expandBuffer()
                    return element
                }
                state === null || state === BUFFERING -> if (segm.casState(i, state, BROKEN)) {
                    expandBuffer()
                    return FAILED_RESULT
                }
                state === CANCELLED -> return FAILED_RESULT
                state === OFFER -> if (segm.casState(i, state, CANCELLED)) return FAILED_RESULT
                state === RESUMING_SENDER -> continue
                else -> {
                    if (segm.casState(i, state, RESUMING_SENDER)) {
                        val helpExpandBuffer = state is ExpandBufferDesc
                        val waiter = if (state is ExpandBufferDesc) state.waiter else state
                        val element = segm.retrieveElement(i)
                        val success = when {
                            waiter === INTERRUPTED -> false
                            waiter is CancellableContinuation<*> -> waiter.tryResumeSend()
                            waiter is NewSelectInstance<*> -> waiter.trySelect(this@BufferedChannel, Unit)
                            else -> error("Unexpected state: $state")
                        }
                        return if (success) {
                            segm.setState(i, DONE)
                            expandBuffer()
                            element
                        } else {
                            if (!segm.casState(i, RESUMING_SENDER, CANCELLED) || helpExpandBuffer)
                                expandBuffer()
                            FAILED_RESULT
                        }
                    }
                }
            }
        }
    }

    private suspend fun receiveSuspend(segm: ChannelSegment<E>, i: Int) = suspendCancellableCoroutineReusable<E> { cont ->
        storeReceiver(
            segm, i, cont,
            onElimination = { w, e -> w.resume(e) },
            cancellationSetup = { cont.invokeOnCancellation { segm.onCancellation(i) } }
        )
    }

    private inline fun <W> storeReceiver(
        segm: ChannelSegment<E>,
        i: Int,
        waiter: W,
        onElimination: (waiter: W, element: E) -> Unit,
        cancellationSetup: (waiter: W) -> Unit
    ) {
        while (true) {
            val state = segm.getState(i)
            when {
                state === null -> if (segm.casState(i, state, waiter)) {
                    onReceiveEnqueued()
                    cancellationSetup(waiter)
                    break
                }
                state === BUFFERING -> {
                    if (segm.casState(i, state, waiter)) break
                }
                state === BUFFERED -> {
                    val element: E = segm.retrieveElement(i)
                    onElimination(waiter, element)
                    break
                }
                else -> error("Unexpected state: $state")
            }
        }
        expandBuffer()
    }

    private fun expandBuffer() {
        if (rendezvous || unlimited) return
        var segm = bufferEndSegment.value
        try_again@while (true) {
            val b = bufferEnd.getAndIncrement()
            val s = senders.value
            if (s <= b) return
            val id = b / SEGMENT_SIZE
            val i = (b % SEGMENT_SIZE).toInt()
            if (segm.id != id) segm = findSegmentBuffer(id, segm)
            if (segm.id != id) {
                bufferEnd.compareAndSet(b + 1, segm.id * SEGMENT_SIZE)
                continue@try_again
            }
            while (true) {
                val state = segm.getState(i)
                when {
                    state === null -> if (segm.casState(i, null, BUFFERING)) return
                    state === CANCELLED -> continue@try_again
                    state === BROKEN || state === OFFER || state === BUFFERED || state === DONE -> return
                    receivers.value > b -> if (segm.casState(i, state, ExpandBufferDesc(state))) return
                    segm.casState(i, state, RESUMING_SENDER) -> { // cont or select
                        val success = when {
                            state === INTERRUPTED -> false
                            state is CancellableContinuation<*> -> state.tryResumeSend()
                            state is NewSelectInstance<*> -> state.trySelect(this@BufferedChannel, Unit)
                            else -> error("Unexpected waiter: $state")
                        }
                        if (success) {
                            segm.setState(i, BUFFERED)
                            return
                        } else {
                            segm.setState(i, CANCELLED)
                            continue@try_again
                        }
                    }
                }
            }
        }
    }

    private fun findSegmentBuffer(id: Long, start: ChannelSegment<E>) =
        bufferEndSegment.findSegmentAndMoveForward(id, start, ::createSegment).segment

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

    private fun registerSelectForSend(select: NewSelectInstance<*>, element: Any?) {
        while (true) {
            trySendRendezvous(
                startSegment = this.sendSegment.value,
                element = element as E,
                onRendezvous = { select.selectInRegPhase(Unit); return },
                oRendezvousFailed = { segm, i, s ->
                    if (storeSender(
                            segm, i, element, s,
                            waiter = select,
                            onRendezvous = { select.selectInRegPhase(Unit); return },
                            cancellationSetup = { select.invokeOnCompletion { segm.onCancellation(i) } }
                        )) return
                })
        }
    }

    private fun registerSelectForReceive(select: NewSelectInstance<*>, ignoredParam: Any?): Unit =
        tryReceiveRendezvousUnit(
            onRendezvous = { e -> select.selectInRegPhase(e); },
            oRendezvousFailed = { segm, i ->
                storeReceiver(
                    segm, i,
                    waiter = select,
                    onElimination = { w, e -> select.selectInRegPhase(e); },
                    cancellationSetup = { select.invokeOnCompletion { segm.onCancellation(i) } }
                )
            }
        )

    private fun processResultSelectSend(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CLOSED_RESULT) throw sendException
        else this

    private fun processResultSelectReceive(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CLOSED_RESULT) throw receiveException
        else selectResult

    private fun processResultSelectReceiveOrNull(ignoredParam: Any?, selectResult: Any?): Any? =
        if (selectResult === CLOSED_RESULT) {
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

    public override fun close(cause: Throwable?): Boolean {
        val closedByThisOperation = closeCause.compareAndSet(NO_CLOSE_CAUSE, cause)
        closed.value = true
        removeWaitingRequests()
        return if (closedByThisOperation) {
            // onClosed() TODO
            invokeCloseHandler()
            true
        } else false
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

//    final override fun cancel(cause: Throwable?): Boolean = cancelImpl(cause)
//    final override fun cancel() { cancelImpl(null) }
//    final override fun cancel(cause: CancellationException?) { cancelImpl(cause) }

//    public fun cancelImpl(cause: Throwable?): Boolean {
//        val closedByThisOperation = close(cause)
//        removeRemainingBufferedElements()
//        return closedByThisOperation
//    }

//    private fun removeRemainingBufferedElements() {
//        var cur: ChannelSegment? = tail
//        while (cur !== null) {
//            for (i in SEGMENT_SIZE - 1 downTo 0) {
//                cur.setWaiterConditionally(i, BROKEN) { it !== BROKEN }
//                cur.onSlotCleaned()
//            }
//            cur = cur.prev.value
//        }
//    }

    private fun removeWaitingRequests() {
//        closeQueue()
//        var cur: ChannelSegment? = tail
//        while (cur != null) {
//            for (i in SEGMENT_SIZE - 1 downTo 0) {
//                val w = cur.getAndSetWaiterConditionally(i, BROKEN) { it !== BUFFERED_OR_DONE && it !== BROKEN }
//                if (w === FAILED_RESULT || w === null) continue
//                when (w) {
//                    is CancellableContinuation<*> -> {
//                        w as CancellableContinuation<Boolean>
//                        cur.setElementLazy(i, CLOSED_RESULT)
//                        w.resume(true)
//                    }
//                    is SelectInstance<*> -> {
//                        w.trySelect(this, CLOSED_RESULT)
//                    }
//                    else -> error("Unknown waiter type: $w")
//                }
//            }
//            cur = cur.prev.value
//        }
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
            return if (result == CLOSED_RESULT) {
                if (closeCause.value == null) {
                    false
                } else {
                    throw (closeCause.value as Throwable)
                }
            } else true
        }

        private fun checkNotClosed(result: Any?): Boolean {
            return if (result === CLOSED_RESULT) {
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
                CLOSED_RESULT -> throw receiveException
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
        get() = TODO("Not yet implemented")
    override val onSend: SelectClause2<E, SendChannel<E>>
        get() = TODO("Not yet implemented")

    override fun trySend(element: E): ChannelResult<Unit> {
        TODO("Not yet implemented")
    }

    @ExperimentalCoroutinesApi
    override val isClosedForReceive: Boolean
        get() = TODO("Not yet implemented")

    @ExperimentalCoroutinesApi
    override val isEmpty: Boolean
        get() = TODO("Not yet implemented")
    override val onReceive: SelectClause1<E>
        get() = TODO("Not yet implemented")

    override suspend fun receiveCatching(): ChannelResult<E> {
        TODO("Not yet implemented")
    }

    override val onReceiveCatching: SelectClause1<ChannelResult<E>>
        get() = TODO("Not yet implemented")

    override fun tryReceive(): ChannelResult<E> {
        TODO("Not yet implemented")
    }

    override fun cancel(cause: CancellationException?) {
        TODO("Not yet implemented")
    }

    override fun cancel(cause: Throwable?): Boolean {
        TODO("Not yet implemented")
    }
}

/**
 * The channel is represented as a list of segments, which simulates an infinite array.
 * Each segment has its own [id], which increase from the beginning. These [id]s help
 * to update [BufferedChannel.head] and [BufferedChannel.tail] correctly
 */
internal class ChannelSegment<E>(id: Long, prev: ChannelSegment<E>?, pointers: Int): Segment<ChannelSegment<E>>(id, prev, pointers) {
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
        setElementLazy(i, null)
        val new = data[i * 2 + 1].updateAndGet {
            when {
                it === RESUMING_SENDER || it === CANCELLED  -> return
                it is ExpandBufferDesc -> ExpandBufferDesc(INTERRUPTED)
                else -> INTERRUPTED
            }
        }
        if (new === CANCELLED) onSlotCleaned()
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

private class ExpandBufferDesc(@JvmField val waiter: Any) {
    override fun toString() = "ExpandBufferDesc($waiter)"
}

// Number of cells in each segment
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.bufferedChannel.segmentSize", 32)

// Cell states
private val BUFFERING = Symbol("BUFFERING")
private val BUFFERED = Symbol("BUFFERED")
private val RESUMING_SENDER = Symbol("RESUMING_SENDER")
private val CANCELLED = Symbol("CANCELLED")
private val BROKEN = Symbol("BROKEN")
private val DONE = Symbol("DONE")
private val OFFER = Symbol("OFFER")
private val INTERRUPTED = Symbol("INTERRUPTED")


// Special values for `CLOSE_HANDLER`
private val CLOSE_HANDLER_CLOSED = Symbol("CLOSE_HANDLER_CLOSED")
private val CLOSE_HANDLER_INVOKED = Symbol("CLOSE_HANDLER_INVOKED")
// Specifies the absence of close cause
private val NO_CLOSE_CAUSE = Symbol("NO_CLOSE_CAUSE")

// Special return values
private val CLOSED_RESULT = Symbol("CLOSED")
private val NO_RESULT = Symbol("NO_RESULT")
private val FAILED_RESULT = Symbol("FAILED")
private val NULL_ELEMENT = Symbol("NULL")
