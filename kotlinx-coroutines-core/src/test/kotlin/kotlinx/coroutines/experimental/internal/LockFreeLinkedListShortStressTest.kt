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

import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Test
import java.util.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.concurrent.thread

/**
 * This stress test has 6 threads adding randomly first or last item to the list and them immediately undoing
 * this addition by remove, and 4 threads removing first node. The resulting list that is being
 * stressed is very short.
 */
class LockFreeLinkedListShortStressTest {
    private data class IntNode(val i: Int) : LockFreeLinkedListNode()
    private val list = LockFreeLinkedListHead()

    val threads = mutableListOf<Thread>()
    val nAdderThreads = 6
    val nRemoverThreads = 4
    val timeout = 5000L
    val completedAdder = AtomicInteger()
    val completedRemover = AtomicInteger()

    val undone = AtomicInteger()
    val missed = AtomicInteger()
    val removed = AtomicInteger()

    @Test
    fun testStress() {
        val deadline = System.currentTimeMillis() + timeout
        repeat(nAdderThreads) { threadId ->
            threads += thread(start = false, name = "adder-$threadId") {
                val rnd = Random()
                while (System.currentTimeMillis() < deadline) {
                    val node = IntNode(threadId)
                    when (rnd.nextInt(4)) {
                        0 -> list.addFirst(node)
                        1 -> list.addLast(node)
                        2 -> list.addFirstIf(node, { true }) // just to test conditional add
                        3 -> list.addLastIf(node, { true })
                    }
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
                while (System.currentTimeMillis() < deadline) {
                    val node = list.removeFirstOrNull()
                    if (node != null) removed.incrementAndGet()

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
        assertEquals(nAdderThreads, completedAdder.get())
        assertEquals(nRemoverThreads, completedRemover.get())
        assertEquals(missed.get(), removed.get())
        assertTrue(undone.get() > 0)
        assertTrue(missed.get() > 0)
        list.validate()
    }
}