@file:OptIn(ExperimentalThreadBlockingApi::class, ExperimentalAtomicApi::class)

package kotlinx.coroutines.testing

import kotlinx.atomicfu.locks.*
import kotlin.concurrent.atomics.*
import kotlin.time.*

// Adapted from kotlinx-atomicfu
// https://github.com/Kotlin/kotlinx-atomicfu/blob/d09c2b07cd16b0b273bd94edaa4929acd2ec42bc/atomicfu/src/concurrentTest/kotlin/kotlinx/atomicfu/locks/CyclicBarrierTest.kt#L59

class TwoPhaseBarrier(private val parties: Int) {
    init {
        require(parties > 1) { "parties must be > 1, but was: $parties" }
    }

    private val queue = MSQueueCyclicBarrier<HandleWrapper>()
    val numberWaiting: Long get() = queue.counterValue


    fun await() {
        val wrapper = HandleWrapper(ParkingSupport.currentThreadHandle())
        val n = queue.enqueue(wrapper)
        if (n % parties == 0L) {
            var wokenUp = 0
            while (wokenUp < parties - 1) {
                val deq = queue.dequeue() ?: error("CyclicBarrier await failed to dequeue")
                if (deq.first % parties == 0L) continue
                if (deq.second.woken.compareAndSet(false, true)) {
                    ParkingSupport.unpark(deq.second.handle)
                    wokenUp++
                }
            }
        } else {
            while (!wrapper.woken.load()) {
                ParkingSupport.park(Duration.INFINITE)
                if (wrapper.reset.load()) {
                    throw Exception("reset was called while this thread was still awaiting")
                }
            }
        }
    }

    fun reset() {

    }
}


private class HandleWrapper(val handle: ParkingHandle) {
    val woken = AtomicBoolean(false)
    val reset = AtomicBoolean(false)
}


private class MSQueueCyclicBarrier<E> {
    private val head = AtomicReference(Node<E>(null, 0))
    private val tail = AtomicReference<Node<E>>(head.load())
    private val counter = AtomicLong(0L)
    val counterValue: Long
        get() = counter.load()

    fun enqueue(element: E): Long {
        while (true) {
            val curTail = tail.load()
            val node = Node(element, curTail.id + 1)
            if (curTail.next.compareAndSet(null, node)) {
                tail.compareAndSet(curTail, node)
                counter.incrementAndFetch()
                return node.id
            } else tail.compareAndSet(curTail, curTail.next.load()!!)
        }
    }

    fun dequeue(): Pair<Long, E>? {
        while (true) {
            val currentHead = head.load()
            val currentHeadNext = currentHead.next.load() ?: return null
            if (head.compareAndSet(currentHead, currentHeadNext)) {
                val element = currentHeadNext.element
                currentHeadNext.element = null
                val id = currentHeadNext.id
                counter.decrementAndFetch()
                return element?.let { Pair(id, it) }
            }
        }
    }

    private class Node<E>(var element: E?, val id: Long) {
        val next = AtomicReference<Node<E>?>(null)
    }
}
