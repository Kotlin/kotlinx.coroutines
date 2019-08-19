/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

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
internal open class BufferedChannel<E>(capacity: Int) : Channel<E>, SegmentQueue<BCSegment>() {
    override fun newSegment(id: Long, prev: BCSegment?) = BCSegment(id, prev)

    init {
        require(capacity >= 0) { "Invalid channel capacity: $capacity, should be >=0" }
    }

    private val unlimited = capacity == Channel.UNLIMITED
    private val rendezvous = capacity == Channel.RENDEZVOUS

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

    /**
     * Invoked when channel is closed as the last action of [closeQueue] invocation.
     * This method should be idempotent and can be called multiple times.
     */
    protected open fun onClosed() {}

    // #########################
    // ## Indices Maintenance ##
    // #########################

    private val senders = atomic(0L)
    private val receivers = atomic(0L)
    private val bufferEnd = atomic(capacity.toLong())
    private val closed = atomic(false)

    @ExperimentalCoroutinesApi
    override val isEmpty: Boolean
        get() = TODO("not implemented") //To change initializer of created properties use File | Settings | File Templates.

    // ######################
    // ## Send and Receive ##
    // ######################

    override fun offer(element: E): Boolean {
        TODO()
    }

    protected fun offerConflated(element: E) {
        offer(element)
        // TODO
//        val senders = sendUnlimited(element)
//        if (senders == -1L) return
//
//        val firstSegmentId = senders / SEGMENT_SIZE
//        var curSegment = findOrCreateSegment(senders / SEGMENT_SIZE, this.head.value)
//        while (curSegment !== null) {
//            val maxIndex = if (curSegment.id == firstSegmentId) ((senders - 1) % SEGMENT_SIZE).toInt() else (SEGMENT_SIZE - 1)
//            for (i in maxIndex downTo 0) {
//                var waiter = curSegment.getCont(i)
//                while (waiter === null) waiter = curSegment.getCont(i)
//                if (waiter === CONT_BUFFERED) curSegment.clean(i)
//            }
//            curSegment = curSegment.prev.value
//        }
    }

    override suspend fun send(element: E) {
        try_again@while (true) {
            if (closed.value) throw sendException
            val h = this.head
            val t = this.tail
            val s = senders.getAndIncrement()
            val b = bufferEnd.value
            val id = s / SEGMENT_SIZE
            val i = (s % SEGMENT_SIZE).toInt()
            if (s < b) { // rendezvous or buffering
                val a = getSegmentAndMoveHead(h, id) ?: continue@try_again
                a.setElementLazy(i, element)
                val old = a.getAndSetWaiterConditionally(i, BUFFERED_OR_DONE) { it !== BROKEN }
                if (old === FAILED_RESULT) continue@try_again
                when (old) {
                    is CancellableContinuation<*> -> {
                        if (old.tryResume()) return
                        else a.setElementLazy(i, null)
                    }
                    is SelectInstance<*> -> { // rendezvous
                        a.setElementLazy(i, null)
                        if (old.trySelect(this, element)) return
                    }
                    else -> return
                }
            } else {
                val a = getSegment(t, id) ?: continue@try_again
                a.setElementLazy(i, element)
                if (sendSuspend(a, i)) return
            }
        }
    }

    private suspend fun sendSuspend(a: BCSegment, i: Int) = suspendAtomicCancellableCoroutine<Boolean> { cont ->
        val old = a.getAndSetWaiterConditionally(i, cont) { it !== BROKEN }
        if (old === BROKEN) cont.resume(false)
        if (old === BUFFERING) cont.resume(true) // already resumed, buffered by race
    }

    override fun poll(): E? {
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

    override suspend fun receive(): E {
        val result = receiveInternal()
        if (result === CLOSED_RESULT) {
            throw this.receiveException
        }
        return result as E
    }

    override suspend fun receiveOrNull(): E? {
        val result = receiveInternal()
        if (result === CLOSED_RESULT) {
            val closeCause = closeCause.value ?: return null
            throw closeCause as Throwable
        }
        return result as E
    }

    private suspend fun receiveInternal(): Any? {
        expandBuffer()
        try_again@while (true) {
            val h = this.head
            val t = this.tail
            val r = this.receivers.getAndIncrement()
            val s = this.senders.value
            val id = r / SEGMENT_SIZE
            val i = (r % SEGMENT_SIZE).toInt()
            if (r < s) {
                val a = getSegmentAndMoveHead(h, id) ?: continue@try_again
                var w: Any?
                read_waiter@while (true) {
                    w = a.getWaiter(i)
                    when {
                        w === null || w === BUFFERING -> continue@read_waiter
                        w === BROKEN -> continue@try_again
                        else -> if (a.casWaiter(i, w, BUFFERED_OR_DONE)) break@read_waiter
                    }
                }
                val res = a.getElement(i) as E
                a.setElementLazy(i, null)
                when {
                    w === BUFFERED_OR_DONE -> return res // buffered
                    w is CancellableContinuation<*> -> {
                        if (w.tryResume()) return res
                    }
                    w is SelectInstance<*> -> {
                        if (w.trySelect(this, null)) return res
                    }
                    else -> error("Unexpected waiter: $w")
                }
            } else {
                val a = getSegment(t, id) ?: return CLOSED_RESULT
                val res = receiveSuspend(a, i)
                if (res === FAILED_RESULT) continue@try_again
                return res
            }
        }
    }

    private suspend fun receiveSuspend(a: BCSegment, i: Int) = suspendAtomicCancellableCoroutine<Any?> { cont ->
        update_waiter@while (true) {
            val w = a.getWaiter(i)
            when {
                w === null -> if (a.casWaiter(i, w, cont)) break@update_waiter
                w === BUFFERED_OR_DONE -> {
                    val res = a.getElement(i)
                    if (a.getWaiter(i) === BUFFERED_OR_DONE) cont.resume(res)
                    else cont.resume(CLOSED_RESULT)
                    break@update_waiter
                }
                w === BROKEN -> FAILED_RESULT
                w === BUFFERING -> continue@update_waiter
                else -> error("Unexpected waiter: $w")
            }
        }
    }

    private fun expandBuffer() {
        try_again@while (true) {
            val h = this.head // TODO special pointer for bufferEnd
            val b = this.bufferEnd.getAndIncrement()
            val s = this.senders.value
            if (s <= b) return
            val id = b / SEGMENT_SIZE
            val i = (b % SEGMENT_SIZE).toInt()
            val a = getSegment(h, id) ?: continue
            while (true) {
                val w = a.getWaiter(i)
                when {
                    w === null -> if (a.casWaiter(i, null, BUFFERING)) return
                    w === BROKEN -> continue@try_again
                    w === BUFFERED_OR_DONE -> return
                    else -> if (a.casWaiter(i, w, BUFFERING)) when (w) {
                        is CancellableContinuation<*> -> if (w.tryResume()) { a.setWaiter(i, BUFFERED_OR_DONE); return }
                        is SelectInstance<*> -> if (w.trySelect(this, null)) { a.setWaiter(i, BUFFERED_OR_DONE); return }
                    }
                }
            }
        }
    }

    // #######################
    // ## Select Expression ##
    // #######################
    // TODO add SelectClauseXXXImpl
    override val onSend: SelectClause2<E, SendChannel<E>> get() = SelectClause2Impl(
            objForSelect = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForSend as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectSend as ProcessResultFunction
    )

    override val onReceiveOrNull: SelectClause1<E?> get() = SelectClause1Impl(
            objForSelect = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectReceiveOrNull as ProcessResultFunction
    )

    override val onReceive: SelectClause1<E> get() = SelectClause1Impl(
            objForSelect = this@BufferedChannel,
            regFunc = BufferedChannel<*>::registerSelectForReceive as RegistrationFunction,
            processResFunc = BufferedChannel<*>::processResultSelectReceive as ProcessResultFunction
    )

    private fun registerSelectForSend(select: SelectInstance<*>, element: Any?) {
        // TODO
    }

    private fun registerSelectForReceive(select: SelectInstance<*>, ignoredParam: Any?) {
       // TODO
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


    @ExperimentalCoroutinesApi
    override val isClosedForSend: Boolean get() = closed.value

    @ExperimentalCoroutinesApi
    override val isClosedForReceive: Boolean get() {
        if (!isClosedForSend) return false
        removeWaitingRequests()
        // try to find a buffered element
        return isEmpty
    }

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

    override fun close(cause: Throwable?): Boolean {
        val closedByThisOperation = closeCause.compareAndSet(NO_CLOSE_CAUSE, cause)
        closed.value = true
        removeWaitingRequests()
        return if (closedByThisOperation) {
            onClosed()
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

    final override fun cancel(cause: Throwable?): Boolean = cancelImpl(cause)
    final override fun cancel() { cancelImpl(null) }
    final override fun cancel(cause: CancellationException?) { cancelImpl(cause) }

    protected open fun cancelImpl(cause: Throwable?): Boolean {
        val closedByThisOperation = close(cause)
        removeRemainingBufferedElements()
        return closedByThisOperation
    }

    private fun removeRemainingBufferedElements() {
        var cur: BCSegment? = tail
        while (cur !== null) {
            for (i in SEGMENT_SIZE - 1 downTo 0) {
                cur.setWaiterConditionally(i, BROKEN) { it !== BROKEN }
                cur.onSlotCleaned()
            }
            cur = cur.prev.value
        }
    }

    private fun removeWaitingRequests() {
        closeQueue()
        var cur: BCSegment? = tail
        while (cur != null) {
            for (i in SEGMENT_SIZE - 1 downTo 0) {
                val w = cur.getAndSetWaiterConditionally(i, BROKEN) { it !== BUFFERED_OR_DONE && it !== BROKEN }
                if (w === FAILED_RESULT || w === null) continue
                when (w) {
                    is CancellableContinuation<*> -> {
                        w as CancellableContinuation<Unit>
                        cur.setElementLazy(i, CLOSED_RESULT)
                        w.resume(Unit)
                    }
                    is SelectInstance<*> -> {
                        w.trySelect(this, CLOSED_RESULT)
                    }
                    else -> error("Unknown waiter type: $w")
                }
            }
            cur = cur.prev.value
        }
    }

    // ######################
    // ## Iterator Support ##
    // ######################

    // TODO make it extension function after `receiveOrClosed` is added.
    override fun iterator(): ChannelIterator<E> = object : ChannelIterator<E> {
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
internal class BCSegment(id: Long, prev: BCSegment?): Segment<BCSegment>(id, prev) {
    private val slots = atomicArrayOfNulls<Any?>(SEGMENT_SIZE * 2) // 2 registers per slot
    private val cleanedSlots = atomic(0)

    inline fun getElement(index: Int): Any? = slots[index * 2].value
    inline fun setElementLazy(index: Int, value: Any?) {
        slots[index * 2].lazySet(value)
    }

    inline fun getWaiter(index: Int): Any? = slots[index * 2 + 1].value
    inline fun setWaiter(index: Int, value: Any?) {
        slots[index * 2 + 1].value = value
    }
    inline fun setWaiterLazy(index: Int, value: Any?) {
        slots[index * 2 + 1].lazySet(value)
    }
    inline fun casWaiter(index: Int, from: Any?, to: Any?) = slots[index * 2 + 1].compareAndSet(from, to)
    inline fun getAndSetWaiter(index: Int, value: Any?) = slots[index * 2 + 1].getAndSet(value)
    inline fun setWaiterConditionally(index: Int, value: Any?, condition: (current: Any?) -> Boolean): Boolean {
        slots[index * 2 + 1].loop { cur ->
            if (!condition(cur)) return false
            if (slots[index * 2 + 1].compareAndSet(cur, value)) return true
        }
    }
    inline fun getAndSetWaiterConditionally(index: Int, value: Any?, condition: (current: Any?) -> Boolean): Any? {
        slots[index * 2 + 1].loop { cur ->
            if (!condition(cur)) return FAILED_RESULT
            if (slots[index * 2 + 1].compareAndSet(cur, value)) return cur
        }
    }

    override val removed: Boolean
        get() = cleanedSlots.value == SEGMENT_SIZE

    /**
     * Cleans the waiter located by the specified index in this segment.
     */
    fun onSlotCleaned() {
        // Increment the number of cleaned slots and remove this segment if needed
        if (cleanedSlots.incrementAndGet() < SEGMENT_SIZE) return
        remove()
    }
}

private fun CancellableContinuation<*>.tryResume(): Boolean {
    this as CancellableContinuation<Unit>
    val token = tryResume(Unit) ?: return false
    completeResume(token)
    return true
}

// Number of waiters in each segment
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.bufferedChannel.segmentSize", 32)

private fun <T> CancellableContinuation<T>.cleanOnCancellation(segment: BCSegment, position: Int) =
    invokeOnCancellation {
        segment.setWaiterLazy(position, BROKEN)
        segment.onSlotCleaned()
    }

// Special continuation values
private val BUFFERING = Symbol("BUFFERING")
private val BROKEN = Symbol("BROKEN")
private val BUFFERED_OR_DONE = Symbol("BUFFERED_OR_DONE")

// Special values for `CLOSE_HANDLER`
private val CLOSE_HANDLER_CLOSED = Symbol("CLOSE_HANDLER_CLOSED")
private val CLOSE_HANDLER_INVOKED = Symbol("CLOSE_HANDLER_INVOKED")
// Specifies the absence of close cause
private val NO_CLOSE_CAUSE = Symbol("NO_CLOSE_CAUSE")

// Special return values
private val CLOSED_RESULT = Symbol("CLOSED")
private val NO_RESULT = Symbol("NO_RESULT")
private val FAILED_RESULT = Symbol("FAILED")