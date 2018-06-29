/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

import kotlinx.atomicfu.LockFreedomTestEnvironment
import kotlinx.coroutines.experimental.TestBase
import org.junit.Assert.*
import org.junit.Test
import java.util.*
import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.atomic.AtomicReference

/**
 * This stress test has 4 threads adding randomly to the list and them immediately undoing
 * this addition by remove, and 4 threads trying to remove nodes from two lists simultaneously (atomically).
 */
class LockFreeLinkedListAtomicStressLFTest : TestBase() {
    private val env = LockFreedomTestEnvironment("LockFreeLinkedListAtomicStressLFTest")

    data class IntNode(val i: Int) : LockFreeLinkedListNode()

    private val TEST_DURATION_SEC = 5 * stressTestMultiplier

    val nLists = 4
    val nAdderThreads = 4
    val nRemoverThreads = 4

    val lists = Array(nLists) { LockFreeLinkedListHead() }

    val undone = AtomicLong()
    val missed = AtomicLong()
    val removed = AtomicLong()
    val error = AtomicReference<Throwable>()

    @Test
    fun testStress() {
        repeat(nAdderThreads) { threadId ->
            val rnd = Random()
            env.testThread(name = "adder-$threadId") {
                when (rnd.nextInt(4)) {
                    0 -> {
                        val list = lists[rnd.nextInt(nLists)]
                        val node = IntNode(threadId)
                        addLastOp(list, node)
                        randomSpinWaitIntermission()
                        tryRemoveOp(node)
                    }
                    1 -> {
                        // just to test conditional add
                        val list = lists[rnd.nextInt(nLists)]
                        val node = IntNode(threadId)
                        addLastIfTrueOp(list, node)
                        randomSpinWaitIntermission()
                        tryRemoveOp(node)
                    }
                    2 -> {
                        // just to test failed conditional add and burn some time
                        val list = lists[rnd.nextInt(nLists)]
                        val node = IntNode(threadId)
                        addLastIfFalseOp(list, node)
                    }
                    3 -> {
                        // add two atomically
                        val idx1 = rnd.nextInt(nLists - 1)
                        val idx2 = idx1 + 1 + rnd.nextInt(nLists - idx1 - 1)
                        check(idx1 < idx2) // that is our global order
                        val list1 = lists[idx1]
                        val list2 = lists[idx2]
                        val node1 = IntNode(threadId)
                        val node2 = IntNode(-threadId - 1)
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
        env.performTest(TEST_DURATION_SEC) {
            val _undone = undone.get()
            val _missed = missed.get()
            val _removed = removed.get()
            println("  Adders undone $_undone node additions")
            println("  Adders missed $_missed nodes")
            println("Remover removed $_removed nodes")
        }
        error.get()?.let { throw it }
        assertEquals(missed.get(), removed.get())
        assertTrue(undone.get() > 0)
        assertTrue(missed.get() > 0)
        lists.forEach { it.validate() }
    }

    private fun addLastOp(list: LockFreeLinkedListHead, node: IntNode) {
        list.addLast(node)
    }

    private fun addLastIfTrueOp(list: LockFreeLinkedListHead, node: IntNode) {
        assertTrue(list.addLastIf(node, { true }))
    }

    private fun addLastIfFalseOp(list: LockFreeLinkedListHead, node: IntNode) {
        assertFalse(list.addLastIf(node, { false }))
    }

    private fun addTwoOp(list1: LockFreeLinkedListHead, node1: IntNode, list2: LockFreeLinkedListHead, node2: IntNode) {
        val add1 = list1.describeAddLast(node1)
        val add2 = list2.describeAddLast(node2)
        val op = object : AtomicOp<Any?>() {
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

    private fun tryRemoveOp(node: IntNode) {
        if (node.remove())
            undone.incrementAndGet()
        else
            missed.incrementAndGet()
    }

    private fun removeTwoOp(list1: LockFreeLinkedListHead, list2: LockFreeLinkedListHead) {
        val remove1 = list1.describeRemoveFirst()
        val remove2 = list2.describeRemoveFirst()
        val op = object : AtomicOp<Any?>() {
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