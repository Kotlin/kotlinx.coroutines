/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlin.math.min

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
internal open class BufferedChannel<E>(capacity: Int) : Channel<E> {
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
     * Invoked when channel is closed as the last action of [close] invocation.
     * This method should be idempotent and can be called multiple times.
     */
    protected open fun onClosed() {}

    // #########################
    // ## Indices Maintenance ##
    // #########################

    // [       1       ] [2   --   22] [23   --   43] [44  --  64]
    //   "closed" flag     lBufferEnd    lReceivers     lSenders
    private val lowest = atomic((capacity.toLong() % OVERFLOWED_COUNTER_MIN_VALUE) shl (TWO_COUNTER_OFFSETS))
    private @Volatile var hSenders = 0L
    private @Volatile var hReceivers = 0L
    private @Volatile var hBufferEnd = capacity.toLong() / OVERFLOWED_COUNTER_MIN_VALUE
    // number of readers + write lock is held if >= WRITE_LOCK_ACQUIRED
    private val lock = atomic(0)

    private inline fun acquireReadLock() {
        var l = this.lock.incrementAndGet() // increment the number of readers
        while (l > WRITE_LOCK_ACQUIRED) l = this.lock.value // wait until the write lock is releasуed
    }

    private inline fun releaseReadLock() {
        this.lock.decrementAndGet() // decrement the number of readers
    }

    private inline fun tryAcquireWriteLock(): Boolean {
        // check if either read or write lock is acquired
        if (this.lock.value > 0) return false
        // try to acquire the write lock if there is no reader
        return this.lock.compareAndSet(0, WRITE_LOCK_ACQUIRED)
    }

    private inline fun releaseWriteLock() {
        this.lock.addAndGet(-WRITE_LOCK_ACQUIRED)
    }

    private fun fixOverflow(lowest: Long, hSenders: Long, hReceivers: Long, hBufferEnd: Long) {
        val fixSenders = (lowest and COUNTER_MASK) >= OVERFLOWED_COUNTER_MIN_VALUE
        val fixReceivers = ((lowest shr COUNTER_OFFSET) and COUNTER_MASK) >= OVERFLOWED_COUNTER_MIN_VALUE
        val fixBufferEnd = ((lowest shr TWO_COUNTER_OFFSETS) and COUNTER_MASK) >= OVERFLOWED_COUNTER_MIN_VALUE
        while (needToFixOverflow(fixSenders, fixReceivers, fixBufferEnd, hSenders, hReceivers, hBufferEnd)) {
            if (tryAcquireWriteLock()) {
                if (fixSenders && this.hSenders == hSenders) {
                    this.lowest.value -= OVERFLOWED_COUNTER_MIN_VALUE
                    this.hSenders++
                }
                if (fixReceivers && this.hReceivers == hReceivers) {
                    this.lowest.value -= OVERFLOWED_COUNTER_MIN_VALUE shl COUNTER_OFFSET
                    this.hReceivers++
                }
                if (fixBufferEnd && this.hBufferEnd == hBufferEnd) {
                    this.lowest.value -= OVERFLOWED_COUNTER_MIN_VALUE shl TWO_COUNTER_OFFSETS
                    this.hBufferEnd++
                }
                releaseWriteLock()
                break
            }
        }

    }

    private fun needToFixOverflow(fixSenders: Boolean, fixReceivers: Boolean, fixBufferEnd: Boolean,
                                  hSenders: Long, hReceivers: Long, hBufferEnd: Long): Boolean {
        if (fixSenders && this.hSenders == hSenders) return true
        if (fixReceivers && this.hReceivers == hReceivers) return true
        if (fixBufferEnd && this.hBufferEnd == hBufferEnd) return true
        return false
    }

    private inline fun countCounters(
        lowest: Long, hSenders: Long, hReceivers: Long, hBufferEnd: Long,
        block: (senders: Long, receivers: Long, bufferEnd: Long, closed: Boolean) -> Unit
    ) {
        val closed = isClosed(lowest)
        val senders = (lowest and COUNTER_MASK) + (hSenders shl (COUNTER_OFFSET - 1))
        val receivers = ((lowest shr COUNTER_OFFSET) and COUNTER_MASK) + (hReceivers shl (COUNTER_OFFSET - 1))
        val bufferEnd = ((lowest shr TWO_COUNTER_OFFSETS) and COUNTER_MASK) + (hBufferEnd shl (COUNTER_OFFSET - 1))
        block(senders, receivers, bufferEnd, closed)
    }

    private inline fun modifyCounters(
        lowestModification: () -> Long,
        action: (senders: Long, receivers: Long, bufferEnd: Long, closed: Boolean) -> Unit
    ) {
        // Do the modification
        acquireReadLock()
        val l = lowestModification()
        val hSenders = this.hSenders
        val hReceivers = this.hReceivers
        val hBufferEnd = this.hBufferEnd
        releaseReadLock()
        fixOverflow(l, hSenders, hReceivers, hBufferEnd)
        // Count counters and invoke the action
        countCounters(l, hSenders, hReceivers, hBufferEnd) { senders, receivers, bufferEnd, closed ->
            action(senders, receivers, bufferEnd, closed)
        }
    }

    private inline fun incSenders(block: (senders: Long, receivers: Long, bufferEnd: Long, closed: Boolean) -> Unit) {
        modifyCounters({ this.lowest.addAndGet(SEND_INC) }, block)
    }

    private inline fun incReceivers(block: (senders: Long, receivers: Long, bufferEnd: Long, closed: Boolean) -> Unit) {
        modifyCounters({ this.lowest.addAndGet(1L shl COUNTER_OFFSET) }, block)
    }

    private inline fun incBufferEnd(block: (senders: Long, receivers: Long, bufferEnd: Long, closed: Boolean) -> Unit) {
        modifyCounters({ this.lowest.addAndGet(BUFFER_END_INC) }, block)
    }

    private inline fun incReceiversAndBufferEnd(block: (senders: Long, receivers: Long, bufferEnd: Long, closed: Boolean) -> Unit) {
        modifyCounters({ this.lowest.addAndGet(RECEIVE_INC + BUFFER_END_INC) }, block)
    }

    private inline fun incCountersWithCondition(
        condition: (senders: Long, receivers: Long, bufferEnd: Long) -> Boolean,
        lowestModification: (curLowest: Long) -> Boolean,
        action: (success: Boolean, senders: Long, receivers: Long, bufferEnd: Long, closed: Boolean) -> Unit
    ) {
        acquireReadLock()
        while (true) {
            val hSenders = this.hSenders
            val hReceivers = this.hReceivers
            val hBufferEnd = this.hBufferEnd
            val l = this.lowest.value
            countCounters(l, hSenders, hReceivers, hBufferEnd) { senders, receivers, bufferEnd, closed ->
                if (!condition(senders, receivers, bufferEnd)) {
                    releaseReadLock()
                    action(false, -1, -1, -1, closed)
                    return
                }
                if (lowestModification(l)) {
                    releaseReadLock()
                    fixOverflow(l, hSenders, hReceivers, hBufferEnd)
                    action(true, senders, receivers, bufferEnd, closed)
                    return
                }
            }
        }
    }

    private inline fun tryIncSenders(block: (success: Boolean, senders: Long, receivers: Long, bufferEnd: Long, closed: Boolean) -> Unit) {
        incCountersWithCondition(
            { senders, receivers, bufferEnd -> unlimited || senders < receivers || senders < bufferEnd},
            { curLowest -> this.lowest.compareAndSet(curLowest, curLowest + SEND_INC) },
            { success, senders, receivers, bufferEnd, closed -> block(success, senders + 1, receivers, bufferEnd, closed) }
        )
    }

    private inline fun tryIncReceivers(block: (success: Boolean, senders: Long, receivers: Long, bufferEnd: Long, closed: Boolean) -> Unit) {
        incCountersWithCondition(
            { senders, receivers, bufferEnd -> receivers < senders },
            { curLowest -> this.lowest.compareAndSet(curLowest, curLowest + RECEIVE_INC) },
            { success, senders, receivers, bufferEnd, closed -> block(success, senders, receivers + 1, bufferEnd, closed) }
        )
    }

    private inline fun tryIncReceiversAndBufferEnd(block: (success: Boolean, senders: Long, receivers: Long, bufferEnd: Long, closed: Boolean) -> Unit) {
        incCountersWithCondition(
            { senders, receivers, bufferEnd -> receivers < senders },
            { curLowest -> this.lowest.compareAndSet(curLowest, curLowest + RECEIVE_INC + BUFFER_END_INC) },
            { success, senders, receivers, bufferEnd, closed -> block(success, senders, receivers + 1, bufferEnd + 1, closed) }
        )
    }

    private inline fun isClosed(lowest: Long) = (lowest and CLOSED_FLAG) != 0L
    private val closed: Boolean get() = isClosed(this.lowest.value)
    private fun setClosedFlag(action: () -> Unit) {
        acquireReadLock()
        try {
            val lowest = this.lowest.updateAndGet { curLowest -> curLowest or CLOSED_FLAG }
            countCounters(lowest, hSenders, hReceivers, hBufferEnd) { _, _, _, _ -> action() }
        } finally {
            releaseReadLock()
        }
    }

    private companion object {
        private const val WRITE_LOCK_ACQUIRED = Int.MAX_VALUE / 2
        private val COUNTER_OFFSET = systemProp("kotlinx.coroutines.bufferedChannel.counterOffset",
                                     defaultValue = 21, minValue = 2, maxValue = 21)
        private val TWO_COUNTER_OFFSETS = COUNTER_OFFSET * 2
        private val COUNTER_MASK = (1L shl COUNTER_OFFSET) - 1L
        private val SEND_INC = 1L
        private val RECEIVE_INC = 1L shl COUNTER_OFFSET
        private val BUFFER_END_INC = 1L shl TWO_COUNTER_OFFSETS
        private val OVERFLOWED_COUNTER_MIN_VALUE = 1L shl (COUNTER_OFFSET - 1)
        private const val CLOSED_FLAG = 1L shl 63
    }


    // #####################
    // ## Waiters Storage ##
    // #####################

    // The waiters storage is represented as a Michael-Scott queue of segments.
    // These `head` and `tail` pointers reference the first and the last segments in the queue.
    // The only difference is that the first segment is not sentinel in our structure.
    //
    // See `Segment` class as well, which contains a segment removing algorithm.
    private val head: AtomicRef<Segment>
    private val tail: AtomicRef<Segment>

    init {
        // Initialize queue with empty node similar to MS queue
        // algorithm, but this node is just empty, not sentinel.
        val emptyNode = Segment(0, null)
        emptyNode.setCont(0, CONT_CLEANED)
        head = atomic(emptyNode)
        tail = atomic(emptyNode)
    }

    /**
     * Finds or creates segment similarly to [findOrCreateSegment],
     * but updates the [head] reference to the found segment as well.
     */
    private fun getHeadAndUpdate(id: Long, headOrOutdated: Segment): Segment? {
        // Check whether the provided segment has the required `id`
        // and just return it in this case.
        if (headOrOutdated.id == id) {
            return headOrOutdated
        }
        // Find (or even create) the required segment
        // and update the `head` pointer.
        val head = findOrCreateSegment(id, headOrOutdated) ?: return null
        moveHeadForward(head)
        // We should clean `prev` references on `head` updates,
        // so they do not reference to the old segments. However,
        // it is fine to clean the `prev` reference of the new head only.
        // The previous "chain" of segments becomes no longer available from
        // segment queue structure and can be collected by GC.
        //
        // Note, that in practice it would be better to clean `next` references as well,
        // since it helps some GC (on JVM). However, this breaks the algorithm.
        head.prev.value = null
        return head
    }

    /**
     * Finds or creates a segment with the specified [id] if it exists,
     * or with a minimal but greater than the specified `id`
     * (`segment.id >= id`) if the required segment was removed
     * This method starts search from the provided [cur] segment,
     * going by `next` references. Returns `null` if this channels is closed
     * and a new segment should be added.
     */
    private fun findOrCreateSegment(id: Long, cur: Segment): Segment? {
        if (cur.id > id) return null
        // This method goes through `next` references and
        // adds new segments if needed, similarly to the `push` in
        // the Michael-Scott queue algorithm.
        var cur = cur
        while (cur.id < id) {
            var curNext = cur.readNext { n, last -> if (last) return null else n }
            if (curNext == null) {
                // Add a new segment.
                val newTail = Segment(cur.id + 1, cur)
                curNext = if (cur.setNext(newTail)) {
                    if (cur.removed) {
                        cur.remove()
                    }
                    moveTailForward(newTail)
                    newTail
                } else {
                    cur.readNext { n, last -> if (last) return null else n!! }
                }
            }
            cur = curNext
        }
        return cur
    }

    /**
     * Updates [head] to the specified segment
     * if its `id` is greater.
     */
    private fun moveHeadForward(new: Segment) {
        while (true) {
            val cur = head.value
            if (cur.id > new.id) return
            if (this.head.compareAndSet(cur, new)) return
        }
    }

    /**
     * Updates [tail] to the specified segment
     * if its `id` is greater.
     */
    private fun moveTailForward(new: Segment) {
        while (true) {
            val cur = this.tail.value
            if (cur.id > new.id) return
            if (this.tail.compareAndSet(cur, new)) return
        }
    }


    // ######################
    // ## Send and Receive ##
    // ######################

    override fun offer(element: E): Boolean {
        if (unlimited) {
            sendUnlimited(element)
            return true
        }

        if (closed) throw sendException
        while (true) {
            val head = this.head.value
            val tail = this.tail.value
            tryIncSenders { success, senders, receivers, bufferEnd, closed ->
                if (!success) {
                    if (closed && closeCause.value != null) throw sendException
                    return false
                }
                if (senders <= receivers) {
                    if (resumeWaiter(element, head, senders) != FAILED) {
                        onReceiveDequeued()
                        return true
                    }
                } else if (unlimited || senders <= bufferEnd) {
                    if (!storeWaiter(CONT_BUFFERED, element, tail, senders)) throw sendException
                    return true
                } else error("WTF???")
            }
        }
    }

    override fun poll(): E? {
        val result = pollInternal()
        when {
            result === FAILED -> return null
            result === CLOSED -> {
                val closeCause = closeCause.value ?: return null
                throw closeCause as Throwable
            }
            else -> return result as (E?)
        }
    }

    private fun pollInternal(): Any? {
        val startHead = this.head.value
        var startBufferEnd = -1L
        tryIncReceiversAndBufferEnd { success, senders, receivers, bufferEnd, closed ->
            if (!success) return if (closed) CLOSED else FAILED
            val resumeResult = resumeWaiter(Unit, startHead, receivers, closed = closed)
            if (resumeResult != FAILED) {
                if (senders >= bufferEnd) resumeNextWaitingSend(startHead, bufferEnd)
                return resumeResult
            } else {
                startBufferEnd = bufferEnd
            }
        }

        while (true) {
            val head = this.head.value
            tryIncReceivers { success, senders, receivers, bufferEnd, closed ->
                if (!success) return if (closed) CLOSED else FAILED
                val resumeResult = resumeWaiter(Unit, head, receivers, closed = closed)
                if (resumeResult != FAILED) {
                    if (senders >= startBufferEnd) resumeNextWaitingSend(startHead, bufferEnd)
                    return resumeResult
                }
            }
        }
    }

    private fun resumeNextWaitingSend(startHead: Segment, startBufferEnd: Long) {
        if (unlimited || rendezvous) return
        val segment = findOrCreateSegment(startBufferEnd / SEGMENT_SIZE, startHead) ?: return
        val i = (startBufferEnd % SEGMENT_SIZE).toInt()
        if (makeBuffered(segment, i)) return
        resumeNextWaitingSend()
    }

    // return true if we should finish
    private fun makeBuffered(segment: Segment, index: Int): Boolean {
        val waiter = segment.readContBlocking(index, CONT_RESUMING)
        if (segment.getElement(index) === RECEIVER_ELEMENT) return true
        if (waiter === CONT_DONE || waiter === CONT_CLEANED || waiter === CONT_BUFFERED) return true
        when (waiter) {
            is CancellableContinuation<*> -> {
                waiter as CancellableContinuation<Unit>
                val token = waiter.tryResume(Unit)
                if (token !== null) {
                    waiter.completeResume(token)
                    segment.setCont(index, CONT_BUFFERED)
                    return true
                } else {
                    segment.setCont(index, CONT_CLEANED)
                }
            }
            is SelectInstance<*> -> {
                if (waiter.trySelect(this@BufferedChannel, Unit)) {
                    segment.setCont(index, CONT_BUFFERED)
                    return true
                } else {
                    segment.setCont(index, CONT_CLEANED)
                }
            }
        }
        return false
    }

    private fun resumeNextWaitingSend() {
        if (unlimited || rendezvous) return
        var segment = this.head.value
        while (true) {
            incBufferEnd { senders, receivers, bufferEnd, closed ->
                if (senders < bufferEnd) return
                segment = findOrCreateSegment(bufferEnd / SEGMENT_SIZE, segment) ?: return
                val i = (bufferEnd % SEGMENT_SIZE).toInt()
                if (makeBuffered(segment, i)) return
            }
        }
    }

    protected fun offerConflated(element: E) {
        val senders = sendUnlimited(element)
        if (senders == -1L) return

        val firstSegmentId = senders / SEGMENT_SIZE
        var curSegment = findOrCreateSegment(senders / SEGMENT_SIZE, this.head.value)
        while (curSegment !== null) {
            val maxIndex = if (curSegment.id == firstSegmentId) ((senders - 1) % SEGMENT_SIZE).toInt() else (SEGMENT_SIZE - 1)
            for (i in maxIndex downTo 0) {
                var waiter = curSegment.getCont(i)
                while (waiter === null) waiter = curSegment.getCont(i)
                if (waiter === CONT_BUFFERED) curSegment.clean(i)
            }
            curSegment = curSegment.prev.value
        }
    }

    private fun sendUnlimited(element: E): Long {
        if (closed) throw sendException

        while (true) {
            val head = this.head.value
            val tail = this.tail.value

            incSenders { senders, receivers, bufferEnd, closed ->
                if (closed) {
                    storeWaiter(CONT_CLEANED, null, tail, senders)
                    throw sendException
                }
                if (senders <= receivers) {
                    if (resumeWaiter(element, head, senders) != FAILED) {
                        onReceiveDequeued()
                        return -1
                    }
                } else {
                    if (!storeWaiter(CONT_BUFFERED, element, tail, senders)) throw sendException
                    return senders
                }
            }
        }
    }

    override suspend fun send(element: E) {
        if (closed) throw sendException

        while (true) {
            val head = this.head.value
            val tail = this.tail.value

            incSenders { senders, receivers, bufferEnd, closed ->
                if (closed) {
                    storeWaiter(CONT_CLEANED, null, tail, senders)
                    throw sendException
                }
                if (senders <= receivers) {
                    if (resumeWaiter(element, head, senders) != FAILED) {
                        onReceiveDequeued()
                        return
                    }
                } else if (unlimited || senders <= bufferEnd) {
                    if (!storeWaiter(CONT_BUFFERED, element, tail, senders)) throw sendException
                    return
                } else {
                    storeCurContinuationAsWaiter<Unit>(element, tail, senders)
                    return
                }
            }
        }
    }

    override suspend fun receive(): E {
        val result = receiveInternal()
        if (result === CLOSED) {
            throw this.receiveException
        }
        return result as E
    }

    override suspend fun receiveOrNull(): E? {
        val result = receiveInternal()
        if (result === CLOSED) {
            val closeCause = closeCause.value ?: return null
            throw closeCause as Throwable
        }
        return result as E
    }


    // TODO cancel (а может и close) сейчас нелинеаризуем
    private suspend fun receiveInternal(): Any? {
        val startHead = this.head.value
        val startTail = this.tail.value
        var startBufferEnd = -1L
        incReceiversAndBufferEnd { senders, receivers, bufferEnd, closed ->
            if (receivers <= senders) {
                val resumeResult = resumeWaiter(Unit, startHead, receivers, closed = closed)
                if (resumeResult != FAILED) {
                    if (senders >= bufferEnd) resumeNextWaitingSend(startHead, bufferEnd)
                    return resumeResult
                } else {
                    startBufferEnd = bufferEnd
                }
            } else {
                if (closed) return CLOSED
                return storeCurContinuationAsWaiter(RECEIVER_ELEMENT, startTail!!, receivers)
            }
        }

        while (true) {
            val head = this.head.value
            val tail = this.tail.value
            incReceivers { senders, receivers, bufferEnd, closed ->
                if (receivers <= senders) {
                    val resumeResult = resumeWaiter(Unit, head, receivers, closed = closed)
                    if (resumeResult != FAILED) {
                        if (senders >= startBufferEnd) resumeNextWaitingSend(startHead, startBufferEnd)
                        return resumeResult
                    }
                } else {
                    if (closed) return CLOSED
                    if (senders >= startBufferEnd) resumeNextWaitingSend(startHead, startBufferEnd)
                    return storeCurContinuationAsWaiter(RECEIVER_ELEMENT, tail!!, receivers)
                }
            }
        }
//
//        resumeNextWaitingSend()
//        try_again@ while (true) {
//            val head = this.head.value
//            val tail = this.tail.value
//            incReceivers { senders, receivers, bufferEnd, closed ->
//                if (receivers <= senders) {
//                    val resumeResult = resumeWaiter(Unit, head, receivers, closed = closed)
//                    if (resumeResult != FAILED) {
//                        return resumeResult
//                    }
//                } else {
//                    if (closed) return CLOSED
//                    return storeCurContinuationAsWaiter(RECEIVER_ELEMENT, tail!!, receivers)
//                }
//            }
//        }
    }

    private fun resumeWaiter(result: Any?, curHead: Segment, counter: Long,
                             curSelect: SelectInstance<*>? = null, closed: Boolean = false): Any?
    {
        val head = getHeadAndUpdate(counter / SEGMENT_SIZE, curHead) ?: return FAILED
        val i = (counter % SEGMENT_SIZE).toInt()
        val waiter = head.readContBlocking(i, CONT_DONE)
        val element = head.getElement(i)
        head.setElementLazy(i, null)
        when {
            waiter === CONT_CLEANED -> return FAILED
            waiter === CONT_BUFFERED -> return element
            waiter is CancellableContinuation<*> -> {
                waiter as CancellableContinuation<in Any?>
                return if (closed) {
                    if (element === RECEIVER_ELEMENT)
                        waiter.resume(CLOSED)
                    else waiter.resumeWithException(sendException)
                    FAILED
                } else {
                    val resumeToken = waiter.tryResume(result, this) ?: return FAILED
                    waiter.completeResume(resumeToken)
                    element
                }
            }
            waiter is SelectInstance<*> -> {
                return if (waiter.trySelect(this, result, curSelect))
                    element
                else
                    FAILED
            }
            else -> error("Invalid continuation: $waiter")
        }
    }

    /**
     * Invokes [suspendAtomicCancellableCoroutine] and stores a new [CancellableContinuation] as a waiter
     * via [storeWaiter] function. Resumes this continuation with an exception if the channel is closed.
     *
     * TODO: move this logic into [send] and [receive] functions when "[KT-28938] Coroutine tail call optimization
     * TODO: does not work for generic returns that had instantiated to Unit" issue is fixed.
     */
    private suspend fun <RESULT> storeCurContinuationAsWaiter(element: Any?, curTail: Segment, cellId: Long) =
        suspendAtomicCancellableCoroutine<RESULT> sc@{ curCont ->
            val successful = storeWaiter(curCont, element, curTail, cellId)
            if (successful) {
                if (element == RECEIVER_ELEMENT) onReceiveEnqueued()
            } else { // closed
                if (element === RECEIVER_ELEMENT) {
                    curCont as CancellableContinuation<in Any>
                    curCont.resume(CLOSED)
                } else {
                    curCont.resumeWithException(sendException)
                }
            }
        }

    /**
     * Stores the specified pair of waiter and element into the cell with [cellId] id.
     * The provided [curTail] is the tail segment pointer before the incrementing the corresponding
     * (`senders` or `receivers`) counter, it is used to find the required segment using [findOrCreateSegment]
     * function. Returns `true` if the storing is successful, or `false` if this channel is closed.
     */
    private fun storeWaiter(waiter: Any, element: Any?, curTail: Segment, cellId: Long): Boolean {
        val segment = findOrCreateSegment(cellId / SEGMENT_SIZE, curTail) ?: return false
        val position = (cellId % SEGMENT_SIZE).toInt()
        segment.setElementLazy(position, element)
        if (!segment.casCont(position, null, waiter)) {
            segment.setElementLazy(position, null)
            return false
        }
        when (waiter) {
            is CancellableContinuation<*> -> {
                waiter.cleanOnCancellation(segment, position)
            }
            is SelectInstance<*> -> {
               waiter.invokeOnCompletion { segment.clean(position) }
            }
        }
        return true
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
        element as E
        if (closed) throw sendException

        while (true) {
            val head = this.head.value
            val tail = this.tail.value

            incSenders { senders, receivers, bufferEnd, closed ->
                if (closed) {
                    storeWaiter(CONT_CLEANED, null, tail, senders)
                    throw sendException
                }
                if (senders <= receivers) {
                    if (resumeWaiter(element, head, senders) != FAILED) {
                        onReceiveDequeued()
                        select.selectInRegPhase(Unit)
                        return
                    }
                } else if (unlimited || senders <= bufferEnd) {
                    if (!storeWaiter(CONT_BUFFERED, element, tail, senders)) throw sendException
                    select.selectInRegPhase(Unit)
                    return
                } else {
                    val successful = storeWaiter(select, element, tail, senders)
                    if (!successful) { // closed
                        throw sendException
                    }
                    return
                }
            }
        }
    }

    private fun registerSelectForReceive(select: SelectInstance<*>, ignoredParam: Any?) {
        val startHead = this.head.value
        val startTail = this.tail.value
        var startBufferEnd = -1L
        incReceiversAndBufferEnd { senders, receivers, bufferEnd, closed ->
            if (receivers <= senders) {
                val resumeResult = resumeWaiter(Unit, startHead, receivers, closed = closed)
                if (resumeResult != FAILED) {
                    if (senders >= bufferEnd) resumeNextWaitingSend(startHead, bufferEnd)
                    select.selectInRegPhase(resumeResult)
                    return
                } else {
                    startBufferEnd = bufferEnd
                }
            } else {
                if (closed) {
                    select.selectInRegPhase(CLOSED)
                    return
                }
                val successful = storeWaiter(select, RECEIVER_ELEMENT, startTail, receivers)
                if (successful) {
                    onReceiveEnqueued()
                    return
                } else { // closed
                    select.selectInRegPhase(CLOSED)
                    return
                }
            }
        }

        while (true) {
            val head = this.head.value
            val tail = this.tail.value
            incReceivers { senders, receivers, bufferEnd, closed ->
                if (receivers <= senders) {
                    val resumeResult = resumeWaiter(Unit, head, receivers, closed = closed)
                    if (resumeResult != FAILED) {
                        if (senders >= startBufferEnd) resumeNextWaitingSend(startHead, startBufferEnd)
                        select.selectInRegPhase(resumeResult)
                        return
                    }
                } else {
                    if (closed) {
                        select.selectInRegPhase(CLOSED)
                        return
                    }
                    val successful = storeWaiter(select, RECEIVER_ELEMENT, tail, receivers)
                    if (successful) {
                        if (senders >= startBufferEnd) resumeNextWaitingSend(startHead, startBufferEnd)
                        onReceiveEnqueued()
                        return
                    } else { // closed
                        select.selectInRegPhase(CLOSED)
                        return
                    }
                }
            }
        }
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


    @ExperimentalCoroutinesApi
    override val isClosedForSend: Boolean
        get() = isClosed(this.lowest.value).also { if (it) removeWaitingRequests(false) }

    @ExperimentalCoroutinesApi
    override val isClosedForReceive: Boolean get() {
        val closed = isClosedForSend
        if (!closed) return false
        removeWaitingRequests(false)
        val tail = this.tail.value
        var head = this.head.value

        while (true) {
            incCountersWithCondition(
                sc@ { senders, receivers, bufferEnd ->
                    val r = receivers + 1
                    head = findOrCreateSegment(r / SEGMENT_SIZE, head) ?: return true.also { releaseReadLock(); }
                    if (r > senders) { releaseReadLock(); return true }
                    if (r > (tail.id + 1) * SEGMENT_SIZE) { releaseReadLock(); return true }
                    val waiter = head.getCont((r % SEGMENT_SIZE).toInt())
                    if (waiter === CONT_BUFFERED) { releaseReadLock(); return false }
                    true
                },
                { curLowest -> this.lowest.compareAndSet(curLowest, curLowest + RECEIVE_INC) },
                {_, _, _, _, _ -> }
            )
        }
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
        setClosedFlag {
            removeWaitingRequests(false)
        }
        return if (closedByThisOperation) {
            onClosed()
            invokeCloseHandler()
            true
        } else false
    }

    private fun removeWaitingRequests(removeBuffered: Boolean) {
        var curTail: Segment? = markTailAsClosed()
        remove@while (curTail != null) {
            cancel_waiter@ for (i in SEGMENT_SIZE - 1 downTo 0) {
                cancel_cur_waiter@ while (true) {
                    // TODO CONT_RESUMING
                    val cont = curTail.getCont(i)
                    if (cont === CONT_DONE) break@remove
                    if (!removeBuffered && cont === CONT_BUFFERED) continue@cancel_waiter
                    if (cont === CONT_CLEANED) continue@cancel_waiter
                    if (!curTail.casCont(i, cont, CONT_CLEANED)) continue@cancel_cur_waiter
                    if (cont === null) break
                    val el = curTail.getElement(i)
                    when (cont) {
                        is CancellableContinuation<*> -> {
                            if (el === RECEIVER_ELEMENT) {
                                cont as CancellableContinuation<in Any>
                                cont.resume(CLOSED)
                            } else {
                                println(el)
                                cont.resumeWithException(sendException)
                            }
                        }
                        is SelectInstance<*> -> {
                            cont.trySelect(this, CLOSED)
                        }
                        //                        else -> error("Unknown continuation type: $cont")
                    }
                    break
                }
            }
            curTail = curTail.prev.value
        }
    }

    private fun markTailAsClosed(): Segment {
        tail.loop { curTail ->
            curTail.readNext { next, last ->
                if (last) return curTail
                if (next === null) {
                    if (curTail.next.compareAndSet(null, CLOSED))
                        return curTail
                } else {
                    moveTailForward(next)
                }
            }
        }
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
        val curHandler = closeHandler.value
        when (curHandler) {
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
        val closedByThisOperation = closeCause.compareAndSet(NO_CLOSE_CAUSE, cause)
        setClosedFlag {
            removeWaitingRequests(true)
        }
        return if (closedByThisOperation) {
            onClosed()
            invokeCloseHandler()
            true
        } else false
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
        override suspend fun next(): E =
            // Read the already received result or NO_RESULT if [hasNext] has not been invoked yet.
            when (val result = this.result) {
                // Rare case -- [hasNext] has not been invoked, invoke [receive] directly.
                NO_RESULT -> receive() // todo: tail call optimization?
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
}

/**
 * The channel is represented as a list of segments, which simulates an infinite array.
 * Each segment has its own [id], which increase from the beginning. These [id]s help
 * to update [BufferedChannel.head] and [BufferedChannel.tail] correctly
 */
private class Segment(@JvmField val id: Long) {
    constructor(id: Long, prev: Segment?) : this(id) {
        this.prev.value = prev
    }

    // == Waiters Array ==
    private val waiters = atomicArrayOfNulls<Any?>(SEGMENT_SIZE * 2)

    inline fun getElement(index: Int): Any? = waiters[index * 2].value
    inline fun setElement(index: Int, value: Any?) {
        waiters[index * 2].value = value
    }
    inline fun setElementLazy(index: Int, value: Any?) {
        waiters[index * 2].lazySet(value)
    }

    inline fun getCont(index: Int): Any? = waiters[index * 2 + 1].value
    inline fun setCont(index: Int, value: Any?) {
        waiters[index * 2 + 1].value = value
    }
    inline fun setContLazy(index: Int, value: Any?) {
        waiters[index * 2 + 1].lazySet(value)
    }
    inline fun casCont(index: Int, from: Any?, to: Any?) = waiters[index * 2 + 1].compareAndSet(from, to)

    fun readContBlocking(index: Int, replacement: Any): Any {
        read_cont@while (true) {
            val cont = getCont(index)
            when {
                cont === null || cont === CONT_RESUMING -> continue@read_cont
                cont === CONT_DONE || cont === CONT_CLEANED -> return cont
                else -> if (casCont(index, cont, replacement)) return cont
            }
        }
    }

    // == Michael-Scott Queue + Fast Removing from the Middle ==

    // Pointer to the next segments, updates
    // similarly to the Michael-Scott queue algorithm.
    val next = atomic<Any?>(null) // null (not set) | Segment | CLOSED
    // Pointer to the previous non-empty segment (can be null!),
    // updates lazily (see `remove()` function).
    val prev = atomic<Segment?>(null)
    // Number of cleaned waiters in this segment.
    private val cleaned = atomic(0)
    val removed get() = cleaned.value == SEGMENT_SIZE

    inline fun setNext(segment: Segment) = this.next.compareAndSet(null, segment)
    inline fun <T> readNext(action: (next: Segment?, last: Boolean) -> T): T {
        val n = next.value
        return when {
            n === CLOSED -> action(null, true)
            else -> action(n as Segment?, false)
        }
    }

    /**
     * Cleans the waiter located by the specified index in this segment.
     */
    fun clean(index: Int) {
        // Clean the specified waiter and
        // check if all node items are cleaned.
        val cont = getCont(index)
        if (cont == CONT_CLEANED) return // already cleaned
        if (!casCont(index, cont, CONT_CLEANED)) return // already cleaned
        setElement(index, null) // clean the element
        if (cleaned.incrementAndGet() < SEGMENT_SIZE) return
        // Remove this node
        remove()
    }

    /**
     * Removes this node from the waiting queue and cleans all references to it.
     */
    fun remove() {
        var next = readNext { n, last -> if (last || n == null) return else n } // tail can't be removed
        // Find the first non-removed node (tail is always non-removed)
        while (next.removed) {
            next = readNext { n, last -> if (last || n == null) return else n }
        }
        // Find the first non-removed `prev` and remove this node
        var prev = prev.value
        while (true) {
            if (prev == null) {
                next.prev.value = null
                return
            }
            if (prev.removed) {
                prev = prev.prev.value
                continue
            }
            next.movePrevToLeft(prev)
            prev.movePrevNextToRight(next)
            if (next.removed || !prev.removed) return
            prev = prev.prev.value
        }
    }

    /**
     * Update [Segment.next] pointer to the specified one if
     * the `id` of the specified segment is greater.
     */
    private fun movePrevNextToRight(next: Segment) {
        while (true) {
            val curNext = this.next.value as Segment
            if (next.id <= curNext.id) return
            if (this.next.compareAndSet(curNext, next)) return
        }
    }

    /**
     * Update [Segment.prev] pointer to the specified segment if
     * its `id` is lower.
     */
    private fun movePrevToLeft(prev: Segment) {
        while (true) {
            val curPrev = this.prev.value ?: return
            if (curPrev.id <= prev.id) return
            if (this.prev.compareAndSet(curPrev, prev)) return
        }
    }
}


// Number of waiters in each segment
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.bufferedChannel.segmentSize", 32)

private fun <T> CancellableContinuation<T>.cleanOnCancellation(segment: Segment, position: Int) =
    invokeOnCancellation { segment.clean(position) }

// Special continuation value for buffered elements
private val CONT_BUFFERED = Symbol("CONT_BUFFERED")
private val CONT_RESUMING = Symbol("CONT_RESUMING")
private val CONT_CLEANED = Symbol("CONT_CLEANED")
private val CONT_DONE = Symbol("CONT_DONE")
// Special values for `CLOSE_HANDLER`
private val CLOSE_HANDLER_CLOSED = Symbol("CLOSE_HANDLER_CLOSED")
private val CLOSE_HANDLER_INVOKED = Symbol("CLOSE_HANDLER_INVOKED")
// Specifies the absence of close cause
private val NO_CLOSE_CAUSE = Symbol("NO_CLOSE_CAUSE")
// Result if the channel is closed
private val CLOSED = Symbol("CLOSED")
// For iterator
private val NO_RESULT = Symbol("NO_RESULT")

private val FAILED = Symbol("FAILED")

private val RECEIVER_ELEMENT = Symbol("RECEIVER_ELEMENT")