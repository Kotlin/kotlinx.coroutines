/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import org.junit.Test
import java.util.*
import java.util.concurrent.atomic.*
import kotlin.concurrent.*
import kotlin.test.*

/**
 * This stress test has 6 threads adding randomly first to the list and them immediately undoing
 * this addition by remove, and 4 threads removing first node. The resulting list that is being
 * stressed is very short.
 */
class LockFreeLinkedListShortStressTest : TestBase() {
    data class IntNode(val i: Int) : LockFreeLinkedListNode()
    val list = LockFreeLinkedListHead()

    private val TEST_DURATION = 5000L * stressTestMultiplier

    val threads = mutableListOf<Thread>()
    private val nAdderThreads = 6
    private val nRemoverThreads = 4
    private val completedAdder = AtomicInteger()
    private val completedRemover = AtomicInteger()

    private val undone = AtomicInteger()
    private val missed = AtomicInteger()
    private val removed = AtomicInteger()

    @Test
    fun testStress() {
        println("--- LockFreeLinkedListShortStressTest")
        val deadline = System.currentTimeMillis() + TEST_DURATION
        repeat(nAdderThreads) { threadId ->
            threads += thread(start = false, name = "adder-$threadId") {
                val rnd = Random()
                while (System.currentTimeMillis() < deadline) {
                    val node = IntNode(threadId)
                    list.addLast(node)
                    if (node.remove()) {
                        undone.incrementAndGet()
                    } else {
                        // randomly help other removal's completion
                        if (rnd.nextBoolean()) node.helpRemove()
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