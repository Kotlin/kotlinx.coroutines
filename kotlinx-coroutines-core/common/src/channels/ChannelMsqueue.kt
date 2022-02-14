/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels


import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.resume
import kotlin.jvm.*

public open class RendezvousChannelMSQueue<E> : Channel<E> {
    protected open fun onReceiveEnqueued() {}
    protected open fun onReceiveDequeued() {}

    private class Node(@JvmField var cont: Any?, @JvmField var element: Any?) {
        private val _next: AtomicRef<Node?> = atomic(null)
        val next: Node? get() = _next.value
        fun casNext(old: Node?, new: Node?): Boolean {
            return _next.compareAndSet(old, new)
        }
    }
    private val _head: AtomicRef<Node>
    private val _tail: AtomicRef<Node>
    init {
        val sentinel = Node(null, null)
        _head = atomic(sentinel)
        _tail = atomic(sentinel)
    }
    override suspend fun send(element: E) {
        // Try to send without suspending at first,
        // invoke suspend implementation if it is not succeed.
        if (offer(element)) return
        sendOrReceiveSuspend<Unit>(element!!)
    }
    override suspend fun receive(): E {
        // Try to send without suspending at first,
        // invoke suspend implementation if it is not succeed.
        val res = poll()
        if (res != null) return res
        return sendOrReceiveSuspend(RECEIVER_ELEMENT)
    }
    override open fun offer(element: E): Boolean {
        return sendOrReceiveNonSuspend<Unit>(element!!) != null
    }
    override fun poll(): E? {
        return sendOrReceiveNonSuspend(RECEIVER_ELEMENT)
    }

    public fun offerUnlimited(element: E): Boolean {
        val node = Node(UNLIMITED_CONTINUATION, element)
        try_again@ while (true) { // CAS loop
            val tail = _tail.value
            val head = _head.value
            if (head == tail) { // the waiting queue is empty
                if (addToQueue(tail, node)) {
                    return true
                } else continue@try_again
            }
            val makeRendezvous = if (element === RECEIVER_ELEMENT) tail.element != RECEIVER_ELEMENT else tail.element == RECEIVER_ELEMENT
            if (!makeRendezvous) {
                if (addToQueue(tail, node)) {
                    return true
                } else continue@try_again
            } else {
                val headNext = head.next
                if (removeHead(head, headNext, tail)) {
                    headNext!!
                    val cont = headNext.cont as CancellableContinuation<in Any?>
                    var res = headNext.element
                    if (res == RECEIVER_ELEMENT) res = Unit
                    headNext.cont = null
                    headNext.element = null
                    val elementForCont = if (element == RECEIVER_ELEMENT) Unit else element
                    onReceiveDequeued()
                    if (cont.tryResumeCont(elementForCont)) {
                        return true
                    } else continue@try_again
                }
            }
        }
    }

    private suspend fun <T> sendOrReceiveSuspend(element: Any) = suspendCancellableCoroutineReusable<T> sc@ { curCont ->
        val node = Node(curCont, element)
        try_again@ while (true) { // CAS loop
            val tail = _tail.value
            val head = _head.value
            if (head == tail) { // the waiting queue is empty
                if (addToQueue(tail, node)) {
                    if (element === RECEIVER_ELEMENT) onReceiveEnqueued()
                    return@sc
                } else continue@try_again
            }
            val makeRendezvous = if (element === RECEIVER_ELEMENT) tail.element != RECEIVER_ELEMENT else tail.element == RECEIVER_ELEMENT
            if (!makeRendezvous) {
                if (addToQueue(tail, node)) {
                    if (element === RECEIVER_ELEMENT) onReceiveEnqueued()
                    return@sc
                } else continue@try_again
            } else {
                val headNext = head.next
                if (removeHead(head, headNext, tail)) {
                    headNext!!
                    val cont = headNext.cont
                    var res = headNext.element
                    if (res == RECEIVER_ELEMENT) res = Unit
                    headNext.cont = null
                    headNext.element = null
                    val elementForCont = if (element == RECEIVER_ELEMENT) Unit else element
                    if (element !== RECEIVER_ELEMENT) onReceiveDequeued()
                    if (cont === UNLIMITED_CONTINUATION || (cont as CancellableContinuation<in Any>).tryResumeCont(elementForCont)) {
                        curCont.resume(res as T)
                        return@sc
                    } else continue@try_again
                }
            }
        }
    }
    private fun <T> sendOrReceiveNonSuspend(element: Any): T? {
//        if (true) return null
        try_again@ while (true) { // CAS loop
            val tail = _tail.value
            val head = _head.value
            if (head == tail) return null
            val makeRendezvous: Boolean
            makeRendezvous = if (element === RECEIVER_ELEMENT) tail.element != RECEIVER_ELEMENT else tail.element == RECEIVER_ELEMENT
            if (makeRendezvous) {
                val headNext = head.next
                if (removeHead(head, headNext, tail)) {
                    headNext!!
                    val cont = headNext.cont
                    var res = headNext.element
                    if (res == RECEIVER_ELEMENT) res = Unit
                    headNext.cont = null
                    headNext.element = null
                    val elementForCont = if (element == RECEIVER_ELEMENT) Unit else element
                    if (element !== RECEIVER_ELEMENT) onReceiveDequeued()
                    if (cont === UNLIMITED_CONTINUATION || (cont as CancellableContinuation<in Any>).tryResumeCont(elementForCont)) {
                        return res as T
                    } else continue@try_again
                }
            } else return null
        }
    }
    private fun addToQueue(tail: Node, node: Node): Boolean {
        val tailNext = tail.next
        if (tail != _tail.value) return false
        if (tailNext != null) {
            _tail.compareAndSet(tail, tailNext)
        } else {
            if (tail.casNext(null, node)) {
                _tail.compareAndSet(tail, node)
                return true
            }
        }
        return false
    }
    private fun removeHead(head: Node, headNext: Node?, tail: Node): Boolean {
        if (tail != _tail.value || head != _head.value || headNext == null) return false
        return _head.compareAndSet(head, headNext)
    }
    public override val onSend: SelectClause2<E, SendChannel<E>>
        get() = TODO("not implemented")
    public override val onReceive: SelectClause1<E>
        get() = TODO("not implemented")
    private companion object {
        @JvmField
        val RECEIVER_ELEMENT = Any()
        @JvmField val UNLIMITED_CONTINUATION = Any()
    }

    @ExperimentalCoroutinesApi
    override val isClosedForSend: Boolean
        get() = TODO("Not yet implemented")

    override fun trySend(element: E): ChannelResult<Unit> {
        TODO("Not yet implemented")
    }

    override fun close(cause: Throwable?): Boolean {
        TODO("Not yet implemented")
    }

    @ExperimentalCoroutinesApi
    override fun invokeOnClose(handler: (cause: Throwable?) -> Unit) {
        TODO("Not yet implemented")
    }

    @ExperimentalCoroutinesApi
    override val isClosedForReceive: Boolean
        get() = TODO("Not yet implemented")

    @ExperimentalCoroutinesApi
    override val isEmpty: Boolean
        get() = TODO("Not yet implemented")

    override suspend fun receiveCatching(): ChannelResult<E> {
        TODO("Not yet implemented")
    }

    override val onReceiveCatching: SelectClause1<ChannelResult<E>>
        get() = TODO("Not yet implemented")

    override fun tryReceive(): ChannelResult<E> {
        TODO("Not yet implemented")
    }

    override fun iterator(): ChannelIterator<E> {
        TODO("Not yet implemented")
    }

    override fun cancel(cause: CancellationException?) {
        TODO("Not yet implemented")
    }

    override fun cancel(cause: Throwable?): Boolean {
        TODO("Not yet implemented")
    }
}