@file:OptIn(ExperimentalThreadBlockingApi::class)

package kotlinx.coroutines.testing

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*
import kotlinx.atomicfu.locks.ParkingHandle
import kotlin.time.*

class CountDownLatch(count: Int) {
    private val c = atomic(count)
    private val waiters = MPSCQueueLatch<ParkingHandle>()

    fun await() {
        val thread = ParkingSupport.currentThreadHandle()
        if (c.value <= 0) return
        if (waiters.enqueue(thread)) {
            while (c.value > 0) {
                ParkingSupport.park(Duration.INFINITE)
            }
        }
    }

    fun countDown() {
        val myIndex = c.decrementAndGet()
        if (myIndex != 0) return
        waiters.drain { ParkingSupport.unpark(it) }
    }
}

private class MPSCQueueLatch<E> {
    private val head = Node<E>(null)
    private val tail = atomic<Node<E>?>(head) // if null, then closed

    fun enqueue(element: E): Boolean {
        val node = Node(element)
        tail.loop {
            if (it == null) return false
            if (it.next.compareAndSet(null, node)) {
                tail.compareAndSet(it, node)
                return true
            } else {
                tail.compareAndSet(it, it.next.value!!)
            }
        }
    }

    fun drain(action: (E) -> Unit) {
        close()
        var node = head.next.value
        while (node != null) {
            action(node.element!!)
            node = node.next.value
        }
        head.next.value = null
    }

    private fun close() {
        tail.loop {
            if (tail.compareAndSet(it, null)) return
        }
    }

    private class Node<E>(var element: E?) {
        val next = atomic<Node<E>?>(null)
    }
}
