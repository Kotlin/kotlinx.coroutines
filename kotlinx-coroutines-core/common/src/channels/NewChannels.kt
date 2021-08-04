package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*

/**
 * This is a common implementation for both rendezvous and buffered channels.
 * Intuitively, the buffered channel allows process first `capacity` [send]s
 * without suspension, storing elements into a virtual buffer.
 * Here a high-level algorithm overview is presented.
 *
 * Each [send] or [receive] operation (other operations are ignored since they are similar)
 * starts by acquiring a ticket, which serves as an index into an infinite array of cells.
 * In order to determine whether the operation should suspend or immediately make a rendezvous
 * or send an element to the virtual buffer, we maintain the following counters atomically:
 *   * `senders` references the cell to work with on the next [send], equals to
 *      the total number of [send] operations on this channel;
 *   * `receivers` references the cell to work with on the next [receive], equals to
 *      the total number of [receive] operations on this channel;
 *   * `bufferEnd` references the end of the virtual buffer.
 * Note, that the `bufferEnd` counter is required since a suspended coroutine or
 * select`-related operation can be cancelled, so it is wrong that `bufferEnd == receivers + capacity`.
 *
 * Depending on these counter values, we can decide whether the operation should suspend or not
 * (these are values in the beginning of the operation):
 *   * [send] -- suspends on `senders > bufferEnd`, stores element on `receivers <= senders <= bufferEnd`,
 *               and makes a rendezvous on `senders < receivers`;
 *   * [receive] -- suspends on `receivers >= senders`, and makes a rendezvous on `receivers < senders`.
 *
 * We update the required counters and take a snapshot at the beginning of each operation.
 * Each [send] operation increments the `senders` counter, while each [receive] increments both
 * `receivers` and `bufferEnd` counters. If [receive] suspends, than it just moves the buffer forward,
 * while on making a rendezvous it
 */
public class BufferedChannel<E>(capacity: Int) {
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

    private val sendSegment: AtomicRef<ChannelSegment>
    private val receiveSegment: AtomicRef<ChannelSegment>
    private val bufferEndSegment: AtomicRef<ChannelSegment>

    private val closed = atomic(false)

    init {
        val s = ChannelSegment(0, null, 3)
        sendSegment = atomic(s)
        receiveSegment = atomic(s)
        bufferEndSegment = atomic(s)
    }

    // ######################
    // ## Send and Receive ##
    // ######################

    public fun offer(element: E): Boolean {
        TODO()
    }

    protected fun offerConflated(element: E) {
        TODO()
    }

    public suspend fun send(element: E) {
        try_again@while (true) {
            checkNotClosedForSend()
            var segm = sendSegment.value
            val s = senders.getAndIncrement()
            val id = s / SEGMENT_SIZE
            val i = (s % SEGMENT_SIZE).toInt()
            segm = sendSegment.findSegmentAndMoveForward(id, segm, ::createSegment).segment
            storeElement(segm, i, element)
            val doNotSuspend = unlimited || s < receivers.value || (!rendezvous && s < bufferEnd.value)
            if (doNotSuspend) { // rendezvous or buffering
                segm.cleanPrev()
                if (trySendWithoutSuspension(segm, i)) return
            } else {
                if(sendSuspend(segm, i, s)) return
            }
        }
    }

    private fun storeElement(segm: ChannelSegment, i: Int, element: E) {
        val element: Any = if (element === null) NULL_VALUE else element
        segm.setElementLazy(i, element)
    }

    private fun trySendWithoutSuspension(segm: ChannelSegment, i: Int, select: NewSelectInstance<*>? = null): Boolean {
        var w = segm.getAndUpdateWaiter(i) { w ->
            when {
                w === null || w === BUFFERING -> BUFFERED // buffering or elimination
                w === BROKEN -> BROKEN // do not change
                w === BROKEN_2 -> BROKEN_2 // do not change
                else -> DONE // SelectInstance or CancellableContinuation
            }
        }
        if (w is ExpandBufferDesc) w = w.cont
        when {
            w === null || w === BUFFERING -> return true
            w === BROKEN -> return false
            w === BROKEN_2 -> return false
            w is CancellableContinuation<*> -> {
                return if (w.tryResumeReceive()) {
                    true
                } else {
                    segm.setElementLazy(i, null)
                    false
                }
            }
            w is NewSelectInstance<*> -> { // rendezvous
                val element = segm.getElement(i)
                segm.setElementLazy(i, null)
                return w.trySelect(objForSelect = this@BufferedChannel, result = element, from = select)
            }
            else -> error("Unexpected waiter: $w")
        }
    }

    private suspend fun sendSuspend(segm: ChannelSegment, i: Int, s: Long) = suspendCancellableCoroutineReusable<Boolean> { cont ->
        val state = segm.getAndSetWaiterConditionally(i, cont) { it !== BROKEN && it !== BROKEN_2 && it !== BUFFERING }
        if (state === BROKEN || state === BROKEN_2) cont.resume(false)
        if (state === BUFFERING) {
            // already resumed, buffered by race
            if (segm.casWaiter(i, BUFFERING, BUFFERED)) cont.resume(true)
            else cont.resume(false)
        }
        if (s < bufferEnd.value) {
            if (segm.casWaiter(i, cont, BUFFERED)) cont.resume(true)
        }
    }

    private fun checkNotClosedForSend() {
        if (closed.value) throw sendException
    }

    public fun poll(): E? {
        val result = pollInternal()
        when {
            result === FAILED_RESULT -> return null
            result === CLOSED_RESULT -> {
                val closeCause = closeCause.value ?: return null
                throw closeCause as Throwable
            }
            else -> return result as (E?)
        }
    }

    private fun pollInternal(): Any? {
        TODO()
    }

    public suspend fun receive(): E {
        val result = receiveInternal()
        if (result === CLOSED_RESULT) {
            throw this.receiveException
        }
        return result as E
    }

    private suspend fun receiveInternal(): Any? {
        while (true) {
            var segm = receiveSegment.value
            val r = this.receivers.getAndIncrement()
            val id = r / SEGMENT_SIZE
            val i = (r % SEGMENT_SIZE).toInt()
            segm = receiveSegment.findSegmentAndMoveForward(id, segm, ::createSegment).segment
            if (r < senders.value) {
                val element = tryReceiveWithoutSuspension(segm, i)
                if (element === FAILED_RESULT) continue
                return element
            } else {
                receiveSuspend(segm, i, r)
                return segm.getElement(i)
            }
        }
    }

    private fun tryReceiveWithoutSuspension(segm: ChannelSegment, i: Int, select: NewSelectInstance<*>? = null): Any? {
        var w: Any?
        read_waiter@while (true) {
            w = segm.getWaiter(i)
            when {
                w === null -> {
                    if (segm.casWaiter(i, null, BROKEN_2)) {
                        expandBuffer()
                        return FAILED_RESULT
                    }
                }
                w === BUFFERING -> {
                    if (segm.casWaiter(i, BUFFERING, BROKEN_2)) {
                        expandBuffer()
                        return FAILED_RESULT
                    }
                }
                w === RESUMING -> continue@read_waiter // TODO how to fix this part?
                w === BROKEN -> return FAILED_RESULT
                else -> if (segm.casWaiter(i, w, RESUMING)) break@read_waiter
            }
        }
        val element = segm.getElement(i) as E
        segm.setElementLazy(i, null)
        val helpExpandBuffer = w is ExpandBufferDesc
        if (w is ExpandBufferDesc) {
            w = w.cont
        }
        when {
            w === BUFFERED -> {
                segm.setWaiter(i, DONE)
                // TODO: re-read the state because of closing?
                select?.selectInRegPhase(element)
                expandBuffer()
                return element
            } // buffered
            w is CancellableContinuation<*> -> {
                if (w.tryResumeSend()) {
                    segm.setWaiter(i, DONE)
                    select?.selectInRegPhase(element)
                    expandBuffer()
                    return element
                } else {
                    if (!segm.casWaiter(i, RESUMING, BROKEN)) expandBuffer()
                    if (helpExpandBuffer) expandBuffer()
                    return FAILED_RESULT
                }
            }
            w is NewSelectInstance<*> -> {
                if (w.trySelect(objForSelect = this@BufferedChannel, result = Unit, from = select)) {
                    segm.setWaiter(i, DONE)
                    select?.selectInRegPhase(element)
                    expandBuffer()
                    return element
                } else {
                    if (!segm.casWaiter(i, RESUMING, BROKEN)) expandBuffer()
                    if (helpExpandBuffer) expandBuffer()
                    return FAILED_RESULT
                }
            }
            else -> error("Unexpected waiter: $w")
        }
    }

    private suspend fun receiveSuspend(segm: ChannelSegment, i: Int, r: Long) = suspendCancellableCoroutineReusable<Unit> { cont ->
        update_waiter@while (true) {
            val w = segm.getWaiter(i)
            when {
                w === null -> if (segm.casWaiter(i, w, cont)) break@update_waiter
                w === BROKEN -> {
                    cont.resumeWithException(receiveException)
                    break@update_waiter
                }
                w === BUFFERING -> {
//                    if (senders.value > r) continue@update_waiter
                    if (segm.casWaiter(i, w, cont)) {
                        break@update_waiter
                    }
                }
                w === BUFFERED -> {
                    cont.resume(Unit)
                    // TODO: re-read the state
                    break@update_waiter
                }
                else -> error("Unexpected waiter: $w")
            }
        }
        expandBuffer()
    }

    override fun toString(): String {
        val data = arrayListOf<String>()
        val head = if (receiveSegment.value.id < sendSegment.value.id) receiveSegment.value else sendSegment.value
        var cur = head
        while (true) {
            repeat(SEGMENT_SIZE) { i ->
                val w = cur.getWaiter(i)
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

    private fun expandBuffer() {
        if (rendezvous || unlimited) return
        try_again@while (true) {
            var segm = bufferEndSegment.value
            val b = bufferEnd.getAndIncrement()
            val s = senders.value
            if (s <= b) return
            val id = b / SEGMENT_SIZE
            val i = (b % SEGMENT_SIZE).toInt()
            segm = bufferEndSegment.findSegmentAndMoveForward(id, segm, ::createSegment).segment
            while (true) {
                val state = segm.getWaiter(i)
                when {
                    state === null -> if (segm.casWaiter(i, null, BUFFERING)) return
                    state === BROKEN -> continue@try_again
                    state === BROKEN_2 -> return
                    state === DONE || state === BUFFERED -> return // already resumed by `receive`
                    state === RESUMING -> if (segm.casWaiter(i, RESUMING, EXPAND_BUFFER)) return
                    receivers.value > b -> if (segm.casWaiter(i, state, ExpandBufferDesc(state))) return
                    segm.casWaiter(i, state, RESUMING) -> when (state) { // cont or select
                        is CancellableContinuation<*> -> {
                            if (state.tryResumeSend()) {
                                segm.setWaiter(i, BUFFERED)
                                return
                            } else {
                                segm.setWaiter(i, BROKEN)
                                continue@try_again
                            }
                        }
                        is NewSelectInstance<*> -> {
                            if (state.trySelect(objForSelect = this@BufferedChannel, result = Unit)) {
                                segm.setWaiter(i, BUFFERED)
                                return
                            } else {
                                segm.setWaiter(i, BROKEN)
                                continue@try_again
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

    public val onSend: NewSelectClause2<E, BufferedChannel<E>>
        get() = NewSelectClause2Impl(
        objForSelect = this@BufferedChannel,
        regFunc = BufferedChannel<*>::registerSelectForSend as RegistrationFunction,
        processResFunc = BufferedChannel<*>::processResultSelectSend as ProcessResultFunction
    )

    public val onReceiveOrNull: NewSelectClause1<E?>
        get() = NewSelectClause1Impl(
        objForSelect = this@BufferedChannel,
        regFunc = BufferedChannel<*>::registerSelectForReceive as RegistrationFunction,
        processResFunc = BufferedChannel<*>::processResultSelectReceiveOrNull as ProcessResultFunction
    )

    public val onReceive: NewSelectClause1<E>
        get() = NewSelectClause1Impl(
        objForSelect = this@BufferedChannel,
        regFunc = BufferedChannel<*>::registerSelectForReceive as RegistrationFunction,
        processResFunc = BufferedChannel<*>::processResultSelectReceive as ProcessResultFunction
    )

    private fun registerSelectForSend(select: NewSelectInstance<*>, element: Any?) {
        try_again@while (true) {
            checkNotClosedForSend()
            var segm = sendSegment.value
            val s = senders.getAndIncrement()
            val id = s / SEGMENT_SIZE
            val i = (s % SEGMENT_SIZE).toInt()
            segm = sendSegment.findSegmentAndMoveForward(id, segm, ::createSegment).segment
            storeElement(segm, i, element as E)
            val doNotSuspend = unlimited || s < receivers.value || (!rendezvous && s < bufferEnd.value)
            if (doNotSuspend) { // rendezvous or buffering
                segm.cleanPrev()
                if (trySendWithoutSuspension(segm = segm, i = i, select = select)) {
                    select.selectInRegPhase(Unit)
                    return
                }
            } else {
                val state = segm.getAndSetWaiterConditionally(i, select) { it !== BROKEN && it !== BROKEN_2 && it !== BUFFERING }
                if (state === BROKEN || state === BROKEN_2) continue@try_again
                if (state === BUFFERING) {
                    if (!segm.casWaiter(i, BUFFERING, BUFFERED)) continue@try_again
                    select.selectInRegPhase(Unit)
                }
                select.invokeOnCompletion { segm.setElementLazy(i, null) }
                if (s < bufferEnd.value) {
                    if (segm.casWaiter(i, select, BUFFERED)) select.selectInRegPhase(Unit)
                }
                return
            }
        }
    }

    private fun registerSelectForReceive(select: NewSelectInstance<*>, ignoredParam: Any?) {
        while (true) {
            var segm = receiveSegment.value
            val r = this.receivers.getAndIncrement()
            val id = r / SEGMENT_SIZE
            val i = (r % SEGMENT_SIZE).toInt()
            segm = receiveSegment.findSegmentAndMoveForward(id, segm, ::createSegment).segment
            if (r < senders.value) {
                val element = tryReceiveWithoutSuspension(segm = segm, i = i, select = select)
                if (element === FAILED_RESULT) continue
                return
            } else {
                update_waiter@while (true) {
                    val w = segm.getWaiter(i)
                    when {
                        w === null -> if (segm.casWaiter(i, w, select)) break@update_waiter
                        w === BROKEN -> {
                            TODO()
                            break@update_waiter
                        }
                        w === BUFFERING -> {
                            if (senders.value > r) continue@update_waiter
                            if (segm.casWaiter(i, w, select)) {
                                break@update_waiter
                            }
                        }
                        w === BUFFERED -> {
                            val element = segm.getElement(i)
                            segm.setElementLazy(i, null)
                            select.selectInRegPhase(element)
                            // TODO: re-read the state
                            break@update_waiter
                        }
                        else -> error("Unexpected waiter: $w")
                    }
                }
                expandBuffer()
                return
            }
        }
    }

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

    public fun close(cause: Throwable?): Boolean {
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

    public fun invokeOnClose(handler: (cause: Throwable?) -> Unit) {
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
    public fun iterator(): ChannelIterator<E> = object : ChannelIterator<E> {
        private var result: Any? = NO_RESULT // NO_RESULT | E (next element) | CLOSED
        override suspend fun hasNext(): Boolean {
            if (result != NO_RESULT) return checkNotClosed(result)
            // Try to receive an element. Store the result even if
            // receiving fails in order to process further [hasNext]
            // and [next] invocations properly.
            result = receiveInternal() // todo: tail call optimization?
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
}

/**
 * The channel is represented as a list of segments, which simulates an infinite array.
 * Each segment has its own [id], which increase from the beginning. These [id]s help
 * to update [BufferedChannel.head] and [BufferedChannel.tail] correctly
 */
internal class ChannelSegment(id: Long, prev: ChannelSegment?, pointers: Int): Segment<ChannelSegment>(id, prev, pointers) {
    private val data = atomicArrayOfNulls<Any?>(SEGMENT_SIZE * 2) // 2 registers per slot

    override val maxSlots: Int get() = SEGMENT_SIZE

    inline fun getElement(index: Int): Any? = data[index * 2].value
    inline fun setElementLazy(index: Int, value: Any?) {
        data[index * 2].lazySet(value)
    }

    inline fun getWaiter(index: Int): Any? = data[index * 2 + 1].value
    inline fun setWaiter(index: Int, value: Any?) {
        data[index * 2 + 1].value = value
    }
    inline fun setWaiterLazy(index: Int, value: Any?) {
        data[index * 2 + 1].lazySet(value)
    }
    inline fun casWaiter(index: Int, from: Any?, to: Any?) = data[index * 2 + 1].compareAndSet(from, to)
    inline fun getAndSetWaiter(index: Int, value: Any?) = data[index * 2 + 1].getAndSet(value)

    inline fun setWaiterConditionally(index: Int, value: Any?, condition: (current: Any?) -> Boolean): Boolean {
        while (true) {
            val cur = data[index * 2 + 1].value
            if (!condition(cur)) return false
            if (data[index * 2 + 1].compareAndSet(cur, value)) return true
        }
    }
    inline fun getAndSetWaiterConditionally(index: Int, value: Any?, condition: (current: Any?) -> Boolean): Any? {
        while (true) {
            val cur = data[index * 2 + 1].value
            if (!condition(cur)) return cur
            if (data[index * 2 + 1].compareAndSet(cur, value)) return cur
        }
    }
    inline fun getAndUpdateWaiter(index: Int, updateFunc: (Any?) -> Any?) = data[index * 2 + 1].getAndUpdate(updateFunc)
}

private fun createSegment(id: Long, prev: ChannelSegment?) = ChannelSegment(id, prev, 0)

private fun CancellableContinuation<*>.tryResumeReceive(): Boolean {
    this as CancellableContinuation<Unit>
    val token = tryResume(Unit) ?: return false
    completeResume(token)
    return true
}

private fun CancellableContinuation<*>.tryResumeSend(): Boolean {
    this as CancellableContinuation<Boolean>
    val token = tryResume(true) ?: return false
    completeResume(token)
    return true
}

private class ExpandBufferDesc(val cont: Any)
private class ReceiveDesc(val cont: CancellableContinuation<*>)

// Number of waiters in each segment
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.bufferedChannel.segmentSize", 32)

private fun <T> CancellableContinuation<T>.cleanOnCancellation(segment: ChannelSegment, position: Int) =
    invokeOnCancellation {
        segment.setWaiterLazy(position, BROKEN)
        segment.onSlotCleaned()
    }

// Special continuation values
private val RESUMING = Symbol("RESUMING")
private val BUFFERING = Symbol("BUFFERING")
private val BUFFERED = Symbol("BUFFERED")
private val BROKEN = Symbol("BROKEN")
private val BROKEN_2 = Symbol("BROKEN_2")
private val DONE = Symbol("DONE")
private val EXPAND_BUFFER = Symbol("EXPAND_BUFFER")


// Special values for `CLOSE_HANDLER`
private val CLOSE_HANDLER_CLOSED = Symbol("CLOSE_HANDLER_CLOSED")
private val CLOSE_HANDLER_INVOKED = Symbol("CLOSE_HANDLER_INVOKED")
// Specifies the absence of close cause
private val NO_CLOSE_CAUSE = Symbol("NO_CLOSE_CAUSE")

// Special return values
private val CLOSED_RESULT = Symbol("CLOSED")
private val NO_RESULT = Symbol("NO_RESULT")
private val FAILED_RESULT = Symbol("FAILED")
private val NULL_VALUE = Symbol("NULL")
