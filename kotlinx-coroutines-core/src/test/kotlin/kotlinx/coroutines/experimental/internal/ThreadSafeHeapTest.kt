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

import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsNull
import org.junit.Assert.assertThat
import org.junit.Test
import java.util.*

class ThreadSafeHeapTest {
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
        assertThat(h.peek(), IsNull())
        val n1 = Node(1)
        h.addLast(n1)
        assertThat(h.peek(), IsEqual(n1))
        val n2 = Node(2)
        h.addLast(n2)
        assertThat(h.peek(), IsEqual(n1))
        val n3 = Node(3)
        h.addLast(n3)
        assertThat(h.peek(), IsEqual(n1))
        val n4 = Node(4)
        h.addLast(n4)
        assertThat(h.peek(), IsEqual(n1))
        val n5 = Node(5)
        h.addLast(n5)
        assertThat(h.peek(), IsEqual(n1))
        assertThat(h.removeFirstOrNull(), IsEqual(n1))
        assertThat(n1.index, IsEqual(-1))
        assertThat(h.peek(), IsEqual(n2))
        h.remove(n2)
        assertThat(h.peek(), IsEqual(n3))
        h.remove(n4)
        assertThat(h.peek(), IsEqual(n3))
        h.remove(n3)
        assertThat(h.peek(), IsEqual(n5))
        h.remove(n5)
        assertThat(h.peek(), IsNull())
    }

    @Test
    fun testRandomSort() {
        val n = 1000
        val r = Random(1)
        val h = ThreadSafeHeap<Node>()
        val a = IntArray(n) { r.nextInt() }
        repeat(n) { h.addLast(Node(a[it])) }
        a.sort()
        repeat(n) { assertThat(h.removeFirstOrNull(), IsEqual(Node(a[it]))) }
        assertThat(h.peek(), IsNull())
    }
}