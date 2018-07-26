/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

import kotlinx.coroutines.experimental.*

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
public interface ThreadSafeHeapNode {
    public var index: Int
}

/**
 * Binary heap.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public class ThreadSafeHeap<T> where T: ThreadSafeHeapNode, T: Comparable<T> {
    private var a: Array<T?>? = null

    internal var size = 0

    public val isEmpty: Boolean get() = size == 0

    public fun peek(): T? = firstImpl()

    public fun removeFirstOrNull(): T? =
        if (size > 0) {
            removeAtImpl(0)
        } else
            null

    public inline fun removeFirstIf(predicate: (T) -> Boolean): T? {
        val first = firstImpl() ?: return null
        return if (predicate(first)) {
            removeAtImpl(0)
        } else
            null
    }

    public fun addLast(node: T) {
        addImpl(node)
    }

    public fun addLastIf(node: T, cond: () -> Boolean): Boolean =
        if (cond()) {
            addImpl(node)
            true
        } else
            false

    public fun remove(node: T): Boolean =
        if (node.index < 0) {
            false
        } else {
            removeAtImpl(node.index)
            true
        }

    @PublishedApi
    internal fun firstImpl(): T? = a?.get(0)

    @PublishedApi
    internal fun removeAtImpl(index: Int): T {
        check(size > 0)
        val a = this.a!!
        size--
        if (index < size) {
            swap(index, size)
            val j = (index - 1) / 2
            if (index > 0 && a[index]!! < a[j]!!) {
                swap(index, j)
                siftUpFrom(j)
            } else {
                siftDownFrom(index)
            }
        }
        val result = a[size]!!
        result.index = -1
        a[size] = null
        return result
    }

    @PublishedApi
    internal fun addImpl(node: T) {
        val a = realloc()
        var i = size++
        a[i] = node
        node.index = i
        siftUpFrom(i)
    }

    private tailrec fun siftUpFrom(i: Int) {
        if (i <= 0) return
        val a = a!!
        val j = (i - 1) / 2
        if (a[j]!! <= a[i]!!) return
        swap(i, j)
        siftUpFrom(j)
    }

    private tailrec fun siftDownFrom(i: Int) {
        var j = 2 * i + 1
        if (j >= size) return
        val a = a!!
        if (j + 1 < size && a[j + 1]!! < a[j]!!) j++
        if (a[i]!! <= a[j]!!) return
        swap(i, j)
        siftDownFrom(j)
    }

    @Suppress("UNCHECKED_CAST")
    private fun realloc(): Array<T?> {
        val a = this.a
        return when {
            a == null -> (arrayOfNulls<ThreadSafeHeapNode>(4) as Array<T?>).also { this.a = it }
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
}