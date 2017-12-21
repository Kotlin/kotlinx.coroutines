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

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
public interface HeapNode {
    public var index: Int
}

/**
 * Binary heap.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public class Heap<T> where T: HeapNode, T: Comparable<T> {
    private var a: Array<T?>? = null
    private var size = 0

    public val isEmpty: Boolean get() = size == 0

    public fun peek(): T? = a?.get(0)

    public fun removeFirstOrNull(): T? =
        if (size > 0) {
            removeAtImpl(0)
        } else
            null

    public fun addLast(node: T) {
        val a1 = realloc()
        var i = size++
        a1[i] = node
        node.index = i
        while (i > 0) {
                val j = (i - 1) / 2
                if (a1[j]!! <= a1[i]!!) break
            swap(i, j)
                i = j
            }
    }

    public fun remove(node: T): Boolean =
        if (node.index < 0) {
            false
        } else {
            removeAtImpl(node.index)
            true
        }

    @PublishedApi
    internal fun removeAtImpl(index: Int): T {
        check(size > 0) { "Size must be positive" }
        val a = this.a!!
        size--
        if (index < size) {
            swap(index, size)
            var i = index
            while (true) {
                var j = 2 * i + 1
                if (j >= size) break
                if (j + 1 < size && a[j + 1]!! < a[j]!!) j++
                if (a[i]!! <= a[j]!!) break
                swap(i, j)
                i = j
            }
        }
        val result = a[size]!!
        result.index = -1
        a[size] = null
        return result
    }

    @Suppress("UNCHECKED_CAST")
    private fun realloc(): Array<T?> {
        val a = this.a
        return when {
            a == null -> (arrayOfNulls<HeapNode>(4) as Array<T?>).also { this.a = it }
            size >= a.size -> a.copyOf(size * 2).also { this.a = it }
            else -> a
        }
    }

    private fun swap(i: Int, j: Int) {
        val a = a!!
        val ni = a[j]!!
        val nj = a[i]!!
        a[i] = ni
        a[j] = nj
        ni.index = i
        nj.index = j
    }

    public inline fun removeFirstIf(predicate: (T) -> Boolean): T? {
        val first = peek() ?: return null
        return if (predicate(first)) {
            removeAtImpl(0)
        } else
            null
    }
}