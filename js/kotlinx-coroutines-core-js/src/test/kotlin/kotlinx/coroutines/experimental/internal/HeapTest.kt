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

import kotlin.js.Math
import kotlin.test.*

class HeapTest {
    class Node(val value: Int) : HeapNode, Comparable<Node> {
        override var index = -1
        override fun compareTo(other: Node): Int = value.compareTo(other.value)
        override fun equals(other: Any?): Boolean = other is Node && other.value == value
        override fun hashCode(): Int = value
        override fun toString(): String = "$value"
    }

    @Test
    fun testBasic() {
        val h = Heap<Node>()
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
        val n = 1000
        val h = Heap<Node>()
        val a = IntArray(n) { (Math.random() * 10000).toInt() }
        repeat(n) { h.addLast(Node(a[it])) }
        a.sort()
        repeat(n) { assertEquals(Node(a[it]), h.removeFirstOrNull()) }
        assertEquals(null, h.peek())
    }
}