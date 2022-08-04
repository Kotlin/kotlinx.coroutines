/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*

/**
 * Broadcast channel with array buffer of a fixed [capacity].
 * Sender suspends only when buffer is full due to one of the receives being slow to consume and
 * receiver suspends only when buffer is empty.
 *
 * **Note**, that elements that are sent to this channel while there are no
 * [openSubscription] subscribers are immediately lost.
 *
 * This channel is created by `BroadcastChannel(capacity)` factory function invocation.
 *
 * This implementation uses lock to protect the buffer, which is held only during very short buffer-update operations.
 * The lock at each subscription is also used to manage concurrent attempts to receive from the same subscriber.
 * The lists of suspended senders or receivers are lock-free.
 */
internal class ArrayBroadcastChannel<E>(
    /**
     * Buffer capacity.
     */
    val capacity: Int
) : AbstractSendChannel<E>(null), BroadcastChannel<E> {
    init {
        require(capacity >= 1) { "ArrayBroadcastChannel capacity must be at least 1, but $capacity was specified" }
    }

    /**
     * NB: prior to changing any logic of ArrayBroadcastChannel internals, please ensure that
     * you do not break internal invariants of the SubscriberList implementation on K/N and KJS
     */

    /*
     *  Writes to buffer are guarded by bufferLock, but reads from buffer are concurrent with writes
     *    - Write element to buffer then write "tail" (volatile)
     *    - Read "tail" (volatile), then read element from buffer
     *  So read/writes to buffer need not be volatile
     */
    private val bufferLock = ReentrantLock()
    private val buffer = arrayOfNulls<Any?>(capacity)

    // head & tail are Long (64 bits) and we assume that they never wrap around
    // head, tail, and size are guarded by bufferLock

    private val _head = atomic(0L)
    private var head: Long // do modulo on use of head
        get() = _head.value
        set(value) { _head.value = value }

    private val _tail = atomic(0L)
    private var tail: Long // do modulo on use of tail
        get() = _tail.value
        set(value) { _tail.value = value }
    
    private val _size = atomic(0)
    private var size: Int
        get() = _size.value
        set(value) { _size.value = value }

    @Suppress("DEPRECATION")
    private val subscribers = subscriberList<Subscriber<E>>()

    override val isBufferAlwaysFull: Boolean get() = false
    override val isBufferFull: Boolean get() = size >= capacity

    public override fun openSubscription(): ReceiveChannel<E> =
        Subscriber(this).also {
            updateHead(addSub = it)
        }

    public override fun close(cause: Throwable?): Boolean {
        if (!super.close(cause)) return false
        checkSubOffers()
        return true
    }

    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    override fun cancel(cause: Throwable?): Boolean =
        cancelInternal(cause)

    override fun cancel(cause: CancellationException?) {
        cancelInternal(cause)
    }

    private fun cancelInternal(cause: Throwable?): Boolean =
        close(cause).also {
            for (sub in subscribers) sub.cancelInternal(cause)
        }

    // result is `OFFER_SUCCESS | OFFER_FAILED | Closed`
    override fun offerInternal(element: E): Any {
        bufferLock.withLock {
            // check if closed for send (under lock, so size cannot change)
            closedForSend?.let { return it }
            val size = this.size
            if (size >= capacity) return OFFER_FAILED
            val tail = this.tail
            buffer[(tail % capacity).toInt()] = element
            this.size = size + 1
            this.tail = tail + 1
        }
        // if offered successfully, then check subscribers outside of lock
        checkSubOffers()
        return OFFER_SUCCESS
    }

    private fun checkSubOffers() {
        var updated = false
        var hasSubs = false
        @Suppress("LoopToCallChain") // must invoke `checkOffer` on every sub
        for (sub in subscribers) {
            hasSubs = true
            if (sub.checkOffer()) updated = true
        }
        if (updated || !hasSubs)
            updateHead()
    }

    // updates head if needed and optionally adds / removes subscriber under the same lock
    private tailrec fun updateHead(addSub: Subscriber<E>? = null, removeSub: Subscriber<E>? = null) {
        // update head in a tail rec loop
        var send: Send? = null
        bufferLock.withLock {
            if (addSub != null) {
                addSub.subHead = tail // start from last element
                val wasEmpty = subscribers.isEmpty()
                subscribers.add(addSub)
                if (!wasEmpty) return // no need to update when adding second and etc sub
            }
            if (removeSub != null) {
                subscribers.remove(removeSub)
                if (head != removeSub.subHead) return // no need to update
            }
            val minHead = computeMinHead()
            val tail = this.tail
            var head = this.head
            val targetHead = minHead.coerceAtMost(tail)
            if (targetHead <= head) return // nothing to do -- head was already moved
            var size = this.size
            // clean up removed (on not need if we don't have any subscribers anymore)
            while (head < targetHead) {
                buffer[(head % capacity).toInt()] = null
                val wasFull = size >= capacity
                // update the size before checking queue (no more senders can queue up)
                this.head = ++head
                this.size = --size
                if (wasFull) {
                    while (true) {
                        send = takeFirstSendOrPeekClosed() ?: break // when when no sender
                        if (send is Closed<*>) break // break when closed for send
                        val token = send!!.tryResumeSend(null)
                        if (token != null) {
                            assert { token === RESUME_TOKEN }
                            // put sent element to the buffer
                            buffer[(tail % capacity).toInt()] = (send as Send).pollResult
                            this.size = size + 1
                            this.tail = tail + 1
                            return@withLock // go out of lock to wakeup this sender
                        }
                        // Too late, already cancelled, but we removed it from the queue and need to release resources.
                        // However, ArrayBroadcastChannel does not support onUndeliveredElement, so nothing to do
                    }
                }
            }
            return // done updating here -> return
        }
        // we only get out of the lock normally when there is a sender to resume
        send!!.completeResumeSend()
        // since we've just sent an element, we might need to resume some receivers
        checkSubOffers()
        // tailrec call to recheck
        updateHead()
    }

    private fun computeMinHead(): Long {
        var minHead = Long.MAX_VALUE
        for (sub in subscribers)
            minHead = minHead.coerceAtMost(sub.subHead) // volatile (atomic) reads of subHead
        return minHead
    }

    @Suppress("UNCHECKED_CAST")
    private fun elementAt(index: Long): E = buffer[(index % capacity).toInt()] as E

    private class Subscriber<E>(
        private val broadcastChannel: ArrayBroadcastChannel<E>
    ) : AbstractChannel<E>(null), ReceiveChannel<E> {
        private val subLock = ReentrantLock()

        private val _subHead = atomic(0L)
        var subHead: Long // guarded by subLock
            get() = _subHead.value
            set(value) { _subHead.value = value }

        override val isBufferAlwaysEmpty: Boolean get() = false
        override val isBufferEmpty: Boolean get() = subHead >= broadcastChannel.tail
        override val isBufferAlwaysFull: Boolean get() = error("Should not be used")
        override val isBufferFull: Boolean get() = error("Should not be used")

        override fun close(cause: Throwable?): Boolean {
            val wasClosed = super.close(cause)
            if (wasClosed) {
                broadcastChannel.updateHead(removeSub = this)
                subLock.withLock {
                    subHead = broadcastChannel.tail
                }
            }
            return wasClosed
        }

        // returns true if subHead was updated and broadcast channel's head must be checked
        // this method is lock-free (it never waits on lock)
        @Suppress("UNCHECKED_CAST")
        fun checkOffer(): Boolean {
            var updated = false
            var closed: Closed<*>? = null
        loop@
            while (needsToCheckOfferWithoutLock()) {
                // just use `tryLock` here and break when some other thread is checking under lock
                // it means that `checkOffer` must be retried after every `unlock`
                if (!subLock.tryLock()) break
                val receive: ReceiveOrClosed<E>?
                var result: Any?
                try {
                    result = peekUnderLock()
                    when {
                        result === POLL_FAILED -> continue@loop // must retest `needsToCheckOfferWithoutLock` outside of the lock
                        result is Closed<*> -> {
                            closed = result
                            break@loop // was closed
                        }
                    }
                    // find a receiver for an element
                    receive = takeFirstReceiveOrPeekClosed() ?: break // break when no one's receiving
                    if (receive is Closed<*>) break // noting more to do if this sub already closed
                    val token = receive.tryResumeReceive(result as E) ?: continue
                    assert { token === RESUME_TOKEN }
                    val subHead = this.subHead
                    this.subHead = subHead + 1 // retrieved element for this subscriber
                    updated = true
                } finally {
                    subLock.unlock()
                }
                receive!!.completeResumeReceive(result as E)
            }
            // do close outside of lock if needed
            closed?.also { close(cause = it.closeCause) }
            return updated
        }

        // result is `E | POLL_FAILED | Closed`
        override fun pollInternal(): Any? {
            var updated = false
            val result = subLock.withLock {
                val result = peekUnderLock()
                when {
                    result is Closed<*> -> { /* just bail out of lock */ }
                    result === POLL_FAILED -> { /* just bail out of lock */ }
                    else -> {
                        // update subHead after retrieiving element from buffer
                        val subHead = this.subHead
                        this.subHead = subHead + 1
                        updated = true
                    }
                }
                result
            }
            // do close outside of lock
            (result as? Closed<*>)?.also { close(cause = it.closeCause) }
            // there could have been checkOffer attempt while we were holding lock
            // now outside the lock recheck if anything else to offer
            if (checkOffer())
                updated = true
            // and finally update broadcast's channel head if needed
            if (updated)
                broadcastChannel.updateHead()
            return result
        }

        // Must invoke this check this after lock, because offer's invocation of `checkOffer` might have failed
        // to `tryLock` just before the lock was about to unlocked, thus loosing notification to this
        // subscription about an element that was just offered
        private fun needsToCheckOfferWithoutLock(): Boolean {
            if (closedForReceive != null)
                return false // already closed -> nothing to do
            if (isBufferEmpty && broadcastChannel.closedForReceive == null)
                return false // no data for us && broadcast channel was not closed yet -> nothing to do
            return true // check otherwise
        }

        // guarded by lock, returns:
        //      E - the element from the buffer at subHead
        //      Closed<*> when closed;
        //      POLL_FAILED when there seems to be no data, but must retest `needsToCheckOfferWithoutLock` outside of lock
        private fun peekUnderLock(): Any? {
            val subHead = this.subHead // guarded read (can be non-volatile read)
            // note: from the broadcastChannel we must read closed token first, then read its tail
            // because it is Ok if tail moves in between the reads (we make decision based on tail first)
            val closedBroadcast = broadcastChannel.closedForReceive // unguarded volatile read
            val tail = broadcastChannel.tail // unguarded volatile read
            if (subHead >= tail) {
                // no elements to poll from the queue -- check if closed broads & closed this sub
                // must retest `needsToCheckOfferWithoutLock` outside of the lock
                return closedBroadcast ?: this.closedForReceive ?: POLL_FAILED
            }
            // Get tentative result. This result may be wrong (completely invalid value, including null),
            // because this subscription might get closed, moving channel's head past this subscription's head.
            val result = broadcastChannel.elementAt(subHead)
            // now check if this subscription was closed
            val closedSub = this.closedForReceive
            if (closedSub != null) return closedSub
            // we know the subscription was not closed, so this tentative result is Ok to return
            return result
        }
    }

    // ------ debug ------

    override val bufferDebugString: String
        get() = "(buffer:capacity=${buffer.size},size=$size)"
}
