/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public interface ThreadSafeHeapNode {
    public var heap: ThreadSafeHeap<*>?
    public var index: Int
}

/**
 * Synchronized binary heap.
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public open class ThreadSafeHeap<T> : SynchronizedObject() where T: ThreadSafeHeapNode, T: Comparable<T> {
    private var a: Array<T?>? = null

    private val _size = atomic(0)

    public var size: Int
        get() = _size.value
        private set(value) { _size.value = value }

    public val isEmpty: Boolean get() = size == 0

    public fun clear() = synchronized(this) {
        a?.fill(null)
        _size.value = 0
    }

    public fun peek(): T? = synchronized(this) { firstImpl() }

    public fun removeFirstOrNull(): T? = synchronized(this) {
        if (size > 0) {
            removeAtImpl(0)
        } else {
            null
        }
    }

    // @Synchronized // NOTE! NOTE! NOTE! inline fun cannot be @Synchronized
    public inline fun removeFirstIf(predicate: (T) -> Boolean): T? = synchronized(this) {
        val first = firstImpl() ?: return null
        if (predicate(first)) {
            removeAtImpl(0)
        } else {
            null
        }
    }

    public fun addLast(node: T) = synchronized(this) { addImpl(node) }

    // @Synchronized // NOTE! NOTE! NOTE! inline fun cannot be @Synchronized
    // Condition also receives current first node in the heap
    public inline fun addLastIf(node: T, cond: (T?) -> Boolean): Boolean = synchronized(this) {
        if (cond(firstImpl())) {
            addImpl(node)
            true
        } else {
            false
        }
    }

    public fun remove(node: T): Boolean = synchronized(this) {
        return if (node.heap == null) {
            false
        } else {
            val index = node.index
            assert { index >= 0 }
            removeAtImpl(index)
            true
        }
    }

    @PublishedApi
    internal fun firstImpl(): T? = a?.get(0)

    @PublishedApi
    internal fun removeAtImpl(index: Int): T {
        assert { size > 0 }
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
        assert { result.heap === this }
        result.heap = null
        result.index = -1
        a[size] = null
        return result
    }

    @PublishedApi
    internal fun addImpl(node: T) {
        assert { node.heap == null }
        node.heap = this
        val a = realloc()
        val i = size++
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
