/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import org.junit.Test
import kotlin.test.*

class LockFreeLinkedListTest {
    data class IntNode(val i: Int) : LockFreeLinkedListNode()

    @Test
    fun testSimpleAddLast() {
        val list = LockFreeLinkedListHead()
        assertContents(list)
        val n1 = IntNode(1).apply { list.addLast(this) }
        assertContents(list, 1)
        val n2 = IntNode(2).apply { list.addLast(this) }
        assertContents(list, 1, 2)
        val n3 = IntNode(3).apply { list.addLast(this) }
        assertContents(list, 1, 2, 3)
        val n4 = IntNode(4).apply { list.addLast(this) }
        assertContents(list, 1, 2, 3, 4)
        assertTrue(n1.remove())
        assertContents(list, 2, 3, 4)
        assertTrue(n3.remove())
        assertContents(list, 2, 4)
        assertTrue(n4.remove())
        assertContents(list, 2)
        assertTrue(n2.remove())
        assertFalse(n2.remove())
        assertContents(list)
    }

    @Test
    fun testCondOps() {
        val list = LockFreeLinkedListHead()
        assertContents(list)
        assertTrue(list.addLastIf(IntNode(1)) { true })
        assertContents(list, 1)
        assertFalse(list.addLastIf(IntNode(2)) { false })
        assertContents(list, 1)
        assertTrue(list.addLastIf(IntNode(3)) { true })
        assertContents(list, 1, 3)
        assertFalse(list.addLastIf(IntNode(4)) { false })
        assertContents(list, 1, 3)
    }

    @Test
    fun testAtomicOpsSingle() {
        val list = LockFreeLinkedListHead()
        assertContents(list)
        val n1 = IntNode(1).also { single(list.describeAddLast(it)) }
        assertContents(list, 1)
        val n2 = IntNode(2).also { single(list.describeAddLast(it)) }
        assertContents(list, 1, 2)
        val n3 = IntNode(3).also { single(list.describeAddLast(it)) }
        assertContents(list, 1, 2, 3)
        val n4 = IntNode(4).also { single(list.describeAddLast(it)) }
        assertContents(list, 1, 2, 3, 4)
    }

    private fun single(part: AtomicDesc) {
        val operation = object : AtomicOp<Any?>() {
            init {
                part.atomicOp = this
            }
            override fun prepare(affected: Any?): Any? = part.prepare(this)
            override fun complete(affected: Any?, failure: Any?) = part.complete(this, failure)
        }
        assertTrue(operation.perform(null) == null)
    }

    private fun assertContents(list: LockFreeLinkedListHead, vararg expected: Int) {
        list.validate()
        val n = expected.size
        val actual = IntArray(n)
        var index = 0
        list.forEach<IntNode> { actual[index++] = it.i }
        assertEquals(n, index)
        for (i in 0 until n) assertEquals(expected[i], actual[i], "item $i")
        assertEquals(expected.isEmpty(), list.isEmpty)
    }
}