package channels_new

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.suspendAtomicCancellableCoroutine
import kotlin.coroutines.resume

class RendezvousChannelStack<E> : Channel<E> {

    private class Node(val cont: CancellableContinuation<*>?, val element: Any?, val next: Node?)
    private val _head = atomic<Node?>(null)
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
        try_again@ while (true) { // CAS loop
            val head = _head.value
            if (head == null) { // queue is empty
                val node = Node(curCont, element, head)
                if (_head.compareAndSet(head, node)) {
                    curCont.initCancellability()
                    return@sc
                } else continue@try_again
            }
            val makeRendezvous = if (element === RECEIVER_ELEMENT) head.element != RECEIVER_ELEMENT else head.element == RECEIVER_ELEMENT
            if (makeRendezvous) {
                if (_head.compareAndSet(head, head.next)) {
                    val cont = head.cont as CancellableContinuation<in Any>
                    var res = head.element
                    if (res == RECEIVER_ELEMENT) res = Unit
                    val elementForCont = if (element == RECEIVER_ELEMENT) Unit else element
                    if (cont.tryResumeCont(elementForCont)) {
                        curCont.resume(res as T)
                        return@sc
                    } else continue@try_again
                }
            } else {
                val node = Node(curCont, element, head)
                if (_head.compareAndSet(head, node)) {
                    curCont.initCancellability()
                    return@sc
                }
            }
        }
    }
    private fun <T> sendOrReceiveNonSuspend(element: Any): T? {
        try_again@ while (true) { // CAS loop
            val head = _head.value
            if (head == null) return null // queue is empty
            val makeRendezvous = if (element === RECEIVER_ELEMENT) head.element != RECEIVER_ELEMENT else head.element == RECEIVER_ELEMENT
            if (makeRendezvous) {
                if (_head.compareAndSet(head, head.next)) {
                    val cont = head.cont as CancellableContinuation<in Any>
                    var res = head.element
                    if (res == RECEIVER_ELEMENT) res = Unit
                    val elementForCont = if (element == RECEIVER_ELEMENT) Unit else element
                    if (cont.tryResumeCont(elementForCont)) {
                        return res as T
                    } else continue@try_again
                }
            } else return null
        }
    }
    override val onSend
        get() = TODO("not implemented")
    override val onReceive
        get() = TODO("not implemented")
    private companion object {
        @JvmField val RECEIVER_ELEMENT = Any()
    }
}