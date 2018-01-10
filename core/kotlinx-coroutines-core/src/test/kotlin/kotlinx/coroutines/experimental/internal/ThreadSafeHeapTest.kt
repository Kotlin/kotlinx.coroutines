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

import kotlinx.coroutines.experimental.*
import kotlin.test.*
import java.util.*

class ThreadSafeHeapTest : TestBase() {
    class Node(val value: Int) : ThreadSafeHeapNode, Comparable<Node> {
        override var index = -1
        override fun compareTo(other: Node): Int = value.compareTo(other.value)
        override fun equals(other: Any?): Boolean = other is Node && other.value == value
        override fun hashCode(): Int = value
        override fun toString(): String = "$value"
    }

    @Test
    fun testBasic() {
        val h = ThreadSafeHeap<Node>()
        assertEquals(null, h.peek())
        val n1 = Node(1)
        h.addLast(n1)
        assertEquals(n1, h.peek())
        val n2 = Node(2)
        h.addLast(n2)
        assertEquals(n1, h.peek())
        val n3 = Node(3)
        h.addLast(n3)
        assertEquals(n1, h.peek())
        val n4 = Node(4)
        h.addLast(n4)
        assertEquals(n1, h.peek())
        val n5 = Node(5)
        h.addLast(n5)
        assertEquals(n1, h.peek())
        assertEquals(n1, h.removeFirstOrNull())
        assertEquals(-1, n1.index)
        assertEquals(n2, h.peek())
        h.remove(n2)
        assertEquals(n3, h.peek())
        h.remove(n4)
        assertEquals(n3, h.peek())
        h.remove(n3)
        assertEquals(n5, h.peek())
        h.remove(n5)
        assertEquals(null, h.peek())
    }

    @Test
    fun testRandomSort() {
        val n = 1000 * stressTestMultiplier
        val r = Random(1)
        val h = ThreadSafeHeap<Node>()
        val a = IntArray(n) { r.nextInt() }
        repeat(n) { h.addLast(Node(a[it])) }
        a.sort()
        repeat(n) { assertEquals(Node(a[it]), h.removeFirstOrNull()) }
        assertEquals(null, h.peek())
    }

    @Test
    fun testRandomRemove() {
        val n = 1000 * stressTestMultiplier
        check(n % 2 == 0) { "Must be even" }
        val r = Random(1)
        val h = ThreadSafeHeap<Node>()
        val set = TreeSet<Node>()
        repeat(n) {
            val node = Node(r.nextInt())
            h.addLast(node)
            assertTrue(set.add(node))
        }
        while (!h.isEmpty) {
            // pick random node to remove
            val rndNode: Node
            while (true) {
                val tail = set.tailSet(Node(r.nextInt()))
                if (!tail.isEmpty()) {
                    rndNode = tail.first()
                    break
                }
            }
            assertTrue(set.remove(rndNode))
            assertTrue(h.remove(rndNode))
            // remove head and validate
            val headNode = h.removeFirstOrNull()!! // must not be null!!!
            assertTrue(headNode === set.first(), "Expected ${set.first()}, but found $headNode, remaining size ${h.size}")
            assertTrue(set.remove(headNode))
            assertEquals(set.size, h.size)
        }
    }
}