/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.LockFreedomTestEnvironment
import kotlinx.coroutines.stressTestMultiplier
import org.junit.Test
import java.util.*
import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.atomic.AtomicReference
import kotlin.test.*

/**
 * This stress test has 4 threads adding randomly to the list and them immediately undoing
 * this addition by remove, and 4 threads trying to remove nodes from two lists simultaneously (atomically).
 */
class LockFreeLinkedListAtomicLFStressTest {
    private val env = LockFreedomTestEnvironment("LockFreeLinkedListAtomicLFStressTest")

    private data class Node(val i: Long) : LockFreeLinkedListNode()

    private val nSeconds = 5 * stressTestMultiplier

    private val nLists = 4
    private val nAdderThreads = 4
    private val nRemoverThreads = 4

    private val lists = Array(nLists) { LockFreeLinkedListHead() }

    private val undone = AtomicLong()
    private val missed = AtomicLong()
    private val removed = AtomicLong()
    private val error = AtomicReference<Throwable>()
    private val index = AtomicLong()

    @Test
    fun testStress() {
        repeat(nAdderThreads) { threadId ->
            val rnd = Random()
            env.testThread(name = "adder-$threadId") {
                when (rnd.nextInt(4)) {
                    0 -> {
                        val list = lists[rnd.nextInt(nLists)]
                        val node = Node(index.incrementAndGet())
                        addLastOp(list, node)
                        randomSpinWaitIntermission()
                        tryRemoveOp(node)
                    }
                    1 -> {
                        // just to test conditional add
                        val list = lists[rnd.nextInt(nLists)]
                        val node = Node(index.incrementAndGet())
                        addLastIfTrueOp(list, node)
                        randomSpinWaitIntermission()
                        tryRemoveOp(node)
                    }
                    2 -> {
                        // just to test failed conditional add and burn some time
                        val list = lists[rnd.nextInt(nLists)]
                        val node = Node(index.incrementAndGet())
                        addLastIfFalseOp(list, node)
                    }
                    3 -> {
                        // add two atomically
                        val idx1 = rnd.nextInt(nLists - 1)
                        val idx2 = idx1 + 1 + rnd.nextInt(nLists - idx1 - 1)
                        check(idx1 < idx2) // that is our global order
                        val list1 = lists[idx1]
                        val list2 = lists[idx2]
                        val node1 = Node(index.incrementAndGet())
                        val node2 = Node(index.incrementAndGet())
                        addTwoOp(list1, node1, list2, node2)
                        randomSpinWaitIntermission()
                        tryRemoveOp(node1)
                        randomSpinWaitIntermission()
                        tryRemoveOp(node2)
                    }
                    else -> error("Cannot happen")
                }
            }
        }
        repeat(nRemoverThreads) { threadId ->
            val rnd = Random()
            env.testThread(name = "remover-$threadId") {
                val idx1 = rnd.nextInt(nLists - 1)
                val idx2 = idx1 + 1 + rnd.nextInt(nLists - idx1 - 1)
                check(idx1 < idx2) // that is our global order
                val list1 = lists[idx1]
                val list2 = lists[idx2]
                removeTwoOp(list1, list2)
            }
        }
        env.performTest(nSeconds) {
            val undone = undone.get()
            val missed = missed.get()
            val removed = removed.get()
            println("  Adders undone $undone node additions")
            println("  Adders missed $missed nodes")
            println("Remover removed $removed nodes")
        }
        error.get()?.let { throw it }
        assertEquals(missed.get(), removed.get())
        assertTrue(undone.get() > 0)
        assertTrue(missed.get() > 0)
        lists.forEach { it.validate() }
    }

    private fun addLastOp(list: LockFreeLinkedListHead, node: Node) {
        list.addLast(node)
    }

    private fun addLastIfTrueOp(list: LockFreeLinkedListHead, node: Node) {
        assertTrue(list.addLastIf(node) { true })
    }

    private fun addLastIfFalseOp(list: LockFreeLinkedListHead, node: Node) {
        assertFalse(list.addLastIf(node) { false })
    }

    private fun addTwoOp(list1: LockFreeLinkedListHead, node1: Node, list2: LockFreeLinkedListHead, node2: Node) {
        val add1 = list1.describeAddLast(node1)
        val add2 = list2.describeAddLast(node2)
        val op = object : AtomicOp<Any?>() {
            init {
                add1.atomicOp = this
                add2.atomicOp = this
            }
            override fun prepare(affected: Any?): Any? =
                add1.prepare(this) ?:
                    add2.prepare(this)

            override fun complete(affected: Any?, failure: Any?) {
                add1.complete(this, failure)
                add2.complete(this, failure)
            }
        }
        assertTrue(op.perform(null) == null)
    }

    private fun tryRemoveOp(node: Node) {
        if (node.remove())
            undone.incrementAndGet()
        else
            missed.incrementAndGet()
    }

    private fun removeTwoOp(list1: LockFreeLinkedListHead, list2: LockFreeLinkedListHead) {
        val remove1 = list1.describeRemoveFirst()
        val remove2 = list2.describeRemoveFirst()
        val op = object : AtomicOp<Any?>() {
            init {
                remove1.atomicOp = this
                remove2.atomicOp = this
            }
            override fun prepare(affected: Any?): Any? =
                remove1.prepare(this) ?:
                    remove2.prepare(this)

            override fun complete(affected: Any?, failure: Any?) {
                remove1.complete(this, failure)
                remove2.complete(this, failure)
            }
        }
        val success = op.perform(null) == null
        if (success) removed.addAndGet(2)
    }
}