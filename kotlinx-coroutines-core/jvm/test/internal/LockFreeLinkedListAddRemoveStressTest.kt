/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import java.util.concurrent.*
import kotlin.concurrent.*
import kotlin.test.*

class LockFreeLinkedListAddRemoveStressTest : TestBase() {
    private class Node : LockFreeLinkedListNode()
    
    private val nRepeat = 100_000 * stressTestMultiplier
    private val list = LockFreeLinkedListHead()
    private val barrier = CyclicBarrier(3)
    private val done = atomic(false)
    private val removed = atomic(0)

    @Test
    fun testStressAddRemove() {
        val threads = ArrayList<Thread>()
        threads += testThread("adder") {
            val node = Node()
            list.addLast(node)
            if (node.remove()) removed.incrementAndGet()
        }
        threads += testThread("remover") {
            val node = list.removeFirstOrNull()
            if (node != null) removed.incrementAndGet()
        }
        try {
            for (i in 1..nRepeat) {
                barrier.await()
                barrier.await()
                assertEquals(i, removed.value)
                list.validate()
            }
        } finally {
            done.value = true
            barrier.await()
            threads.forEach { it.join() }
        }
    }

    private fun testThread(name: String, op: () -> Unit) = thread(name = name) {
        while (true) {
            barrier.await()
            if (done.value) break
            op()
            barrier.await()
        }
    }
}