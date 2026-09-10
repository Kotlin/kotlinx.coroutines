@file:OptIn(ExperimentalThreadBlockingApi::class)

package kotlinx.coroutines.testing

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*
import kotlin.time.*


/**
 * Minimalistic multiplatform (JVM + Native) alternative for java.util.concurrent.CountDownLatch.
 *
 * It is not reusable: once the latch has been lifted, it will always stay lifted.
 *
 * No thread interrupts support: an awaiting thread or a coroutine will degrade to a busy-spin if interrupted.
 */
class CountDownLatch(count: Int) {
    init {
        require(count >= 0) { "A negative count doesn't have a meaning. Initialize with 0 to keep the latch lifted from the start." }
    }

    private val c = atomic(count)
    private val waiters = MPSCQueueLatch<ParkingHandle>()

    fun await() {
        tryAwait(Duration.INFINITE)
    }

    fun tryAwait(duration: Duration): Boolean {
        val thread = ParkingSupport.currentThreadHandle()
        if (c.value <= 0) return true
        val start = TimeSource.Monotonic.markNow()
        if (waiters.enqueue(thread)) {
            while (c.value > 0) {
                val remaining = start + duration - TimeSource.Monotonic.markNow()
                if (remaining.isNegative()) return false
                ParkingSupport.park(remaining)
            }
        }
        return true
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
