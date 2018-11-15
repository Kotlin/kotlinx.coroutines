package channels_new

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.suspendAtomicCancellableCoroutine
import kotlin.coroutines.resume

class RendezvousChannelMSQueue<E> : Channel<E> {

    private class Node(@JvmField var cont: CancellableContinuation<*>?, @JvmField var element: Any?) {
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
    override fun offer(element: E): Boolean {
        return sendOrReceiveNonSuspend<Unit>(element!!) != null
    }
    override fun poll(): E? {
        return sendOrReceiveNonSuspend(RECEIVER_ELEMENT)
    }
    private suspend fun <T> sendOrReceiveSuspend(element: Any) = suspendAtomicCancellableCoroutine<T>(holdCancellability = true) sc@ { curCont ->
        val node = Node(curCont, element)
        try_again@ while (true) { // CAS loop
            val tail = _tail.value
            val head = _head.value
            if (head == tail) { // the waiting queue is empty
                if (addToQueue(tail, node)) {
                    curCont.initCancellability()
                    return@sc
                } else continue@try_again
            }
            val makeRendezvous = if (element === RECEIVER_ELEMENT) tail.element != RECEIVER_ELEMENT else tail.element == RECEIVER_ELEMENT
            if (!makeRendezvous) {
                if (addToQueue(tail, node)) {
                    curCont.initCancellability()
                    return@sc
                } else continue@try_again
            } else {
                val headNext = head.next
                if (removeHead(head, headNext, tail)) {
                    headNext!!
                    val cont = headNext.cont as CancellableContinuation<in Any>
                    var res = headNext.element
                    if (res == RECEIVER_ELEMENT) res = Unit
                    headNext.cont = null
                    headNext.element = null
                    val elementForCont = if (element == RECEIVER_ELEMENT) Unit else element
                    if (cont.tryResumeCont(elementForCont)) {
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
                    val cont = headNext.cont as CancellableContinuation<in Any>
                    var res = headNext.element
                    if (res == RECEIVER_ELEMENT) res = Unit
                    headNext.cont = null
                    headNext.element = null
                    val elementForCont = if (element == RECEIVER_ELEMENT) Unit else element
                    if (cont.tryResumeCont(elementForCont)) {
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
    override val onSend
        get() = TODO("not implemented")
    override val onReceive
        get() = TODO("not implemented")
    private companion object {
        @JvmField val RECEIVER_ELEMENT = Any()
    }
}