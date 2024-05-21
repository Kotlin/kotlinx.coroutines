package kotlinx.coroutines.internal

import kotlinx.coroutines.testing.TestBase
import org.junit.Test
import java.util.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.concurrent.thread

/**
 * This stress test has 2 threads adding on one side on list, 2 more threads adding on the other,
 * and 6 threads iterating and concurrently removing items. The resulting list that is being
 * stressed is long.
 */
class LockFreeLinkedListLongStressTest : TestBase() {
    data class IntNode(val i: Int) : LockFreeLinkedListNode()
    val list = LockFreeLinkedListHead()

    val threads = mutableListOf<Thread>()
    private val nAdded = 10_000_000 // should not stress more, because that'll run out of memory
    private val nAddThreads = 4 // must be power of 2 (!!!)
    private val nRemoveThreads = 6
    private val removeProbability = 0.2
    private val workingAdders = AtomicInteger(nAddThreads)

    private fun shallRemove(i: Int) = i and 63 != 42

    @Test
    fun testStress() {
        println("--- LockFreeLinkedListLongStressTest")
        for (j in 0 until nAddThreads)
            threads += thread(start = false, name = "adder-$j") {
                for (i in j until nAdded step nAddThreads) {
                    list.addLast(IntNode(i), Int.MAX_VALUE)
                }
                println("${Thread.currentThread().name} completed")
                workingAdders.decrementAndGet()
            }
        for (j in 0 until nRemoveThreads)
            threads += thread(start = false, name = "remover-$j") {
                val rnd = Random()
                do {
                    val lastTurn = workingAdders.get() == 0
                    list.forEach { node ->
                        if (node is IntNode && shallRemove(node.i) && (lastTurn || rnd.nextDouble() < removeProbability))
                            node.remove()
                    }
                } while (!lastTurn)
                println("${Thread.currentThread().name} completed")
            }
        println("Starting ${threads.size} threads")
        for (thread in threads)
            thread.start()
        println("Joining threads")
        for (thread in threads)
            thread.join()
        // verification
        println("Verify result")
        list.validate()
        val expected = iterator {
            for (i in 0 until nAdded)
                if (!shallRemove(i))
                    yield(i)
        }
        list.forEach { node ->
            require(node !is IntNode || node.i == expected.next())
        }
        require(!expected.hasNext())
    }

    private fun LockFreeLinkedListHead.validate() {
        var prev: LockFreeLinkedListNode = this
        var cur: LockFreeLinkedListNode = next as LockFreeLinkedListNode
        while (cur != this) {
            val next = cur.nextNode
            cur.validateNode(prev, next)
            prev = cur
            cur = next
        }
        validateNode(prev, next as LockFreeLinkedListNode)
    }
}
