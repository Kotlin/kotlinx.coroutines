import kotlinx.atomicfu.locks.ExperimentalThreadBlockingApi
import kotlinx.atomicfu.locks.ParkingHandle
import kotlinx.atomicfu.locks.ParkingSupport
import kotlin.concurrent.atomics.AtomicBoolean
import kotlin.concurrent.atomics.AtomicReference
import kotlin.concurrent.atomics.ExperimentalAtomicApi
import kotlin.test.DefaultAsserter.fail
import kotlin.time.Duration

@OptIn(ExperimentalThreadBlockingApi::class)
private class HandleWrapper(val handle: ParkingHandle) {
    @OptIn(ExperimentalAtomicApi::class)
    val woken = AtomicBoolean(false)
}

public class ConcurrentCyclicBarrier(private val parties: Int) {
    private val queue = MSQueueCyclicBarrier<HandleWrapper>()

    @OptIn(ExperimentalThreadBlockingApi::class, ExperimentalAtomicApi::class)
    fun await() {
        val wrapper = HandleWrapper(ParkingSupport.currentThreadHandle())
        val n = queue.enqueue(wrapper)
        if (n % parties == 0L) {
            var wokenUp = 0
            while (wokenUp < parties - 1) {
                val deq = queue.dequeue()
                //if (deq == null) fail("Not enough parties enqueued")
                if (deq!!.first % parties == 0L) continue
                @Suppress("BooleanLiteralArgument")
                if (deq.second.woken.compareAndSet(false, true)) {
                    ParkingSupport.unpark(deq.second.handle)
                    wokenUp++
                }
            }
        } else {
            while (!wrapper.woken.load()) {
                ParkingSupport.park(Duration.INFINITE)
            }
        }
    }
}

@OptIn(ExperimentalAtomicApi::class)
private class MSQueueCyclicBarrier<E> {
    private val head = AtomicReference(Node<E>(null, 0))
    private val tail = AtomicReference(head.load())

    fun enqueue(element: E): Long {
        while (true) {
            val curTail = tail.load()
            val node = Node(element, curTail.id + 1)
            if (curTail.next.compareAndSet(null, node)) {
                tail.compareAndSet(curTail, node)
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
                return element?.let { Pair(id, it) }
            }
        }
    }

    private class Node<E>(var element: E?, val id: Long) {
        val next = AtomicReference<Node<E>?>(null)
    }
}
