package kotlinx.coroutines.experimental.scheduling

import kotlinx.atomicfu.*

// Interface for tests, actually has only one implementation at runtime
internal interface TaskQueue {
    fun add(value: TimedTask): Boolean
    fun poll(): TimedTask?
    fun pollBlockingMode(): TimedTask?
}

/*
 * Michael & Scott lock-free queue from atomicfu library which supports poll with predicate
 */
internal class LockFreeQueue : TaskQueue {
    private val head =
        atomic(Node(TimedTask(Runnable { throw AssertionError() }, -1, TaskMode.NON_BLOCKING))) // sentinel
    private val tail = atomic(head.value)

    private class Node(val value: TimedTask) {
        val next = atomic<Node?>(null)
    }

    public override fun add(value: TimedTask): Boolean {
        val node = Node(value)
        tail.loop { curTail ->
            val curNext = curTail.next.value
            if (curNext != null) {
                tail.compareAndSet(curTail, curNext)
                return@loop
            }

            if (curTail.next.compareAndSet(null, node)) {
                tail.compareAndSet(curTail, node)
                return true
            }
        }
    }

    public override fun poll(): TimedTask? {
        head.loop { curHead ->
            val next = curHead.next.value ?: return null
            if (head.compareAndSet(curHead, next)) {
                return next.value
            }
        }
    }

    public override fun pollBlockingMode(): TimedTask? {
        head.loop { curHead ->
            val next = curHead.next.value ?: return null
            if (next.value.mode != TaskMode.PROBABLY_BLOCKING) return null
            if (head.compareAndSet(curHead, next)) {
                return next.value
            }
        }
    }

    public fun isEmpty(): Boolean = size() == 0 // For test purposes

    public fun size(): Int {
        var result = 0
        var current = head.value
        while (current.next.value != null) {
            current = current.next.value!!
            ++result

        }

        return result
    }
}