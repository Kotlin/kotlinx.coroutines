/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

import kotlinx.coroutines.experimental.TestBase
import org.junit.Assert.*
import org.junit.Test
import java.util.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.concurrent.thread

/**
 * This stress test has 6 threads adding randomly first to the list and them immediately undoing
 * this addition by remove, and 4 threads removing first node. The resulting list that is being
 * stressed is very short.
 */
class LockFreeLinkedListShortStressTest : TestBase() {
    data class IntNode(val i: Int) : LockFreeLinkedListNode()
    val list = LockFreeLinkedListHead()

    val TEST_DURATION = 5000L * stressTestMultiplier

    val threads = mutableListOf<Thread>()
    val nAdderThreads = 6
    val nRemoverThreads = 4
    val completedAdder = AtomicInteger()
    val completedRemover = AtomicInteger()

    val undone = AtomicInteger()
    val missed = AtomicInteger()
    val removed = AtomicInteger()

    @Test
    fun testStress() {
        println("--- LockFreeLinkedListShortStressTest")
        val deadline = System.currentTimeMillis() + TEST_DURATION
        repeat(nAdderThreads) { threadId ->
            threads += thread(start = false, name = "adder-$threadId") {
                val rnd = Random()
                while (System.currentTimeMillis() < deadline) {
                    var node: IntNode? = IntNode(threadId)
                    when (rnd.nextInt(3)) {
                        0 -> list.addLast(node!!)
                        1 -> assertTrue(list.addLastIf(node!!, { true })) // just to test conditional add
                        2 -> { // just to test failed conditional add
                            assertFalse(list.addLastIf(node!!, { false }))
                            node = null
                        }
                    }
                    if (node != null) {
                        if (node.remove())
                            undone.incrementAndGet()
                        else
                            missed.incrementAndGet()
                    }
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