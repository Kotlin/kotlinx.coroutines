@file:OptIn(ExperimentalThreadBlockingApi::class, ExperimentalAtomicApi::class)

package kotlinx.coroutines.testing

import kotlinx.atomicfu.locks.*
import kotlinx.atomicfu.*
import kotlin.time.*
import kotlin.concurrent.atomics.*
import kotlin.concurrent.atomics.AtomicBoolean

// Adapted from kotlinx-atomicfu
// https://github.com/Kotlin/kotlinx-atomicfu/blob/d09c2b07cd16b0b273bd94edaa4929acd2ec42bc/atomicfu/src/concurrentTest/kotlin/kotlinx/atomicfu/locks/CyclicBarrierTest.kt#L59

class TwoPhaseBarrier(private val parties: Int) {
    init {
        require(parties > 1) { "parties must be > 1, but was: $parties" }
    }

    private val queue = MSQueueCyclicBarrier<HandleWrapper>()

    fun await() {
        val wrapper = HandleWrapper(ParkingSupport.currentThreadHandle())
        val n = queue.enqueue(wrapper)
        if (n % parties == 0L) {
            var wokenUp = 0
            while (true) {
                val wrapper = queue.dequeue() ?: error("CyclicBarrier await failed to dequeue")
                if (wokenUp == parties - 1) break // the current thread was dequeued above, it's already awake
                val awoken = wrapper.woken.compareAndSet(false, true)
                check(awoken)
                ParkingSupport.unpark(wrapper.handle)
                wokenUp++
            }
        } else {
            while (!wrapper.woken.load()) {
                ParkingSupport.park(Duration.INFINITE)
            }
        }
    }
}


private class HandleWrapper(val handle: ParkingHandle) {
    val woken = AtomicBoolean(false)
}


private class MSQueueCyclicBarrier<E> {
    private val head = atomic(Node<E>(null, 0))
    private val tail = atomic<Node<E>>(head.value)

    fun enqueue(element: E): Long {
        while (true) {
            val curTail = tail.value
            val node = Node(element, curTail.id + 1)
            if (curTail.next.compareAndSet(null, node)) {
                tail.compareAndSet(curTail, node)
                return node.id
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

    private class Node<E>(var element: E?, val id: Long) {
        val next = atomic<Node<E>?>(null)
    }
}
