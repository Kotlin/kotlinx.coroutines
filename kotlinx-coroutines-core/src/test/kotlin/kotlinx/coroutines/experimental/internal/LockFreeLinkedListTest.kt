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
    fun testRemoveTwoAtomic() {
        val list = LockFreeLinkedListHead()
        val n1 = IntNode(1).apply { list.addLast(this) }
        val n2 = IntNode(2).apply { list.addLast(this) }
        assertContents(list, 1, 2)
        assertFalse(n1.isRemoved)
        assertFalse(n2.isRemoved)
        val remove1Desc = n1.describeRemove()!!
        val remove2Desc = n2.describeRemove()!!
        val operation = object : AtomicOp<Any?>() {
            override fun prepare(affected: Any?): Any? = remove1Desc.prepare(this) ?: remove2Desc.prepare(this)
            override fun complete(affected: Any?, failure: Any?) {
                remove1Desc.complete(this, failure)
                remove2Desc.complete(this, failure)
            }
        }
        assertTrue(operation.perform(null) == null)
        assertTrue(n1.isRemoved)
        assertTrue(n2.isRemoved)
        assertContents(list)
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
        single(n3.describeRemove()!!)
        assertContents(list, 1, 2, 4)
        assertTrue(n3.describeRemove() == null)
        single(list.describeRemoveFirst())
        assertContents(list, 2, 4)
        assertTrue(n1.describeRemove() == null)
        assertTrue(n2.remove())
        assertContents(list, 4)
        assertTrue(n4.remove())
        assertContents(list)
    }

    private fun single(part: AtomicDesc) {
        val operation = object : AtomicOp<Any?>() {
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
        for (i in 0 until n) assertEquals("item i", expected[i], actual[i])
        assertEquals(expected.isEmpty(), list.isEmpty)
    }
}