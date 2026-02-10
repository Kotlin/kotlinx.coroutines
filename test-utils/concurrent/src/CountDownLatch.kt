@file:OptIn(ExperimentalThreadBlockingApi::class)

package kotlinx.coroutines.testing

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*
import kotlinx.atomicfu.locks.ParkingHandle
import kotlin.time.*

class CountDownLatch(count: Int) {
    private val c = atomic(count)
    private val waiters = MSQueueLatch<ParkingHandle>()

    fun await() {
        val thread = ParkingSupport.currentThreadHandle()
        waiters.enqueue(thread)
        while (c.value > 0) ParkingSupport.park(Duration.INFINITE)
    }

    fun countDown() {
        val myIndex = c.decrementAndGet()
        if (myIndex != 0) return
        while (true) {
            val thread = waiters.dequeue()
            if (thread == null) return
            ParkingSupport.unpark(thread)
        }
    }
}

private class MSQueueLatch<E> {
    private val head = atomic(Node<E>(null))
    private val tail = atomic(head.value)

    fun enqueue(element: E) {
        while (true) {
            val node = Node(element)
            val curTail = tail.value
            if (curTail.next.compareAndSet(null, node)) {
                tail.compareAndSet(curTail, node)
                return
            } else tail.compareAndSet(curTail, curTail.next.value!!)
        }
    }

    fun dequeue(): E? {
        while (true) {
            val currentHead = head.value
            val currentHeadNext = currentHead.next.value ?: return null
            if (head.compareAndSet(currentHead, currentHeadNext)) {
                val element = currentHeadNext.element
                currentHeadNext.element = null
                return element
            }
        }
    }

    private class Node<E>(var element: E?) {
        val next = atomic<Node<E>?>(null)
    }
}
