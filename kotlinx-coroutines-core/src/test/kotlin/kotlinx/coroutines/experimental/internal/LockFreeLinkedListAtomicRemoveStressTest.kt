/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.internal

import org.junit.Assert.*
import org.junit.Test
import java.util.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.concurrent.thread

/**
 * This stress test has 4 threads adding randomly first to the list and them immediately undoing
 * this addition by remove, and 4 threads trying to remove nodes from two lists simultaneously (atomically).
 */
class LockFreeLinkedListAtomicRemoveStressTest {
    data class IntNode(val i: Int) : LockFreeLinkedListNode()

    val threads = mutableListOf<Thread>()
    val nLists = 4
    val nRemoverThreads = 4
    val timeout = 5000L
    val completedAdder = AtomicInteger()
    val completedRemover = AtomicInteger()

    val lists = Array(nLists) { LockFreeLinkedListHead() }

    val undone = AtomicInteger()
    val missed = AtomicInteger()
    val removed = AtomicInteger()

    @Test
    fun testStress() {
        val deadline = System.currentTimeMillis() + timeout
        repeat(nLists) { threadId ->
            threads += thread(start = false, name = "adder-$threadId") {
                val rnd = Random()
                val list = lists[threadId]
                while (System.currentTimeMillis() < deadline) {
                    var node: IntNode? = IntNode(threadId)
                    when (rnd.nextInt(3)) {
                        0 -> list.addLast(node!!)
                        1 -> assertTrue(list.addLastIf(node!!, { true })) // just to test conditional add
                        2 -> { // just to test failed conditional add and burn some time
                            assertFalse(list.addLastIf(node!!, { false }))
                            node = null
                        }
                        else -> error("Cannot happen")
                    }
                    if (node == null) continue
                    when (rnd.nextInt(3)) {
                        0 -> {} // nothing -- be quick
                        1 -> {
                            // burn some time
                            Thread.yield()
                        }
                        2 -> {
                            // burn more time
                            Thread.sleep(1)
                        }
                        else -> error("Cannot happen")
                    }
                    // undo add
                    if (node.remove())
                        undone.incrementAndGet()
                    else
                        missed.incrementAndGet()
                }
                completedAdder.incrementAndGet()
            }
        }
        repeat(nRemoverThreads) { threadId ->
            threads += thread(start = false, name = "remover-$threadId") {
                val rnd = Random()
                while (System.currentTimeMillis() < deadline) {
                    val idx1 = rnd.nextInt(nLists - 1)
                    val idx2 = idx1 + 1 + rnd.nextInt(nLists - idx1 - 1)
                    check(idx1 < idx2) // that is our global order
                    val list1 = lists[idx1]
                    val list2 = lists[idx2]
                    val remove1 = list1.describeRemoveFirst()
                    val remove2 = list2.describeRemoveFirst()
                    val op = object : AtomicOp() {
                        override fun prepare(): Any? = remove1.prepare(this) ?: remove2.prepare(this)
                        override fun complete(affected: Any?, failure: Any?) {
                            remove1.complete(this, failure)
                            remove2.complete(this, failure)
                        }
                    }
                    val success = op.perform(null) == null
                    if (success) removed.addAndGet(2)

                }
                completedRemover.incrementAndGet()
            }
        }
        threads.forEach { it.start() }
        threads.forEach { it.join() }
        println("Completed successfully ${completedAdder.get()} adder threads")
        println("Completed successfully ${completedRemover.get()} remover threads")
        println("  Adders undone ${undone.get()} node additions")
        println("  Adders missed ${missed.get()} nodes")
        println("Remover removed ${removed.get()} nodes")
        assertEquals(nLists, completedAdder.get())
        assertEquals(nRemoverThreads, completedRemover.get())
        assertEquals(missed.get(), removed.get())
        assertTrue(undone.get() > 0)
        assertTrue(missed.get() > 0)
        lists.forEach { it.validate() }
    }
}