@file:OptIn(ExperimentalThreadBlockingApi::class)

package kotlinx.coroutines.testing

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*
import kotlinx.atomicfu.locks.ParkingHandle
import kotlin.time.*

class CountDownLatch(count: Int) {
    private val c = atomic(count)
    private val waiters = MpscStack()

    fun await() {
        val handle = ParkingSupport.currentThreadHandle()
        if (waiters.push(handle)) {
            // Each pushed thread must be parked at least once.
            // Unpark before park makes the next park return immediately.
            // Unpark will be definitely called on each pushed thread in `drain`.
            // So we must counteract the side effects of this unpark.
            do {
                ParkingSupport.park(Duration.INFINITE)
            } while (c.value > 0)
        }
    }

    fun countDown() {
        val count = c.decrementAndGet()
        if (count > 0) return
        if (count < 0) error("Count down to negative value: $count is prohibited.")
        // count == 0, c <= 0
        waiters.drain {
            ParkingSupport.unpark(it)
        }
    }
}

class MpscStack {
    // Invariant: node only stores non-null values. Node(null, _) is a sentinel.
    private class Node(val data: ParkingHandle?, var next: Node?)

    companion object {
        private val sentinel = Node(null, null)
    }

    // Invariant: once head stores null, it will always store null.
    // Head storing null indicates the end of the stack usage. The stack is considered closed.
    // Any further push will return false. Any further drain will drain an empty list.
    private val head = atomic<Node?>(sentinel)

    fun push(element: ParkingHandle): Boolean {
        val node = Node(element, null)
        head.loop { cur ->
            if (cur == null) return false
            node.next = cur
            if (head.compareAndSet(cur, node)) return true
        }
    }

    fun drain(consumer: (ParkingHandle) -> Unit) {
        var node = head.getAndSet(null)
        while (node != null) {
            if (node == sentinel) break
            consumer(node.data!!)
            node = node.next
        }
    }
}
