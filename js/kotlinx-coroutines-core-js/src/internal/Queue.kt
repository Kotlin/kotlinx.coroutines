/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

internal open class Queue<T : Any> {
    private var queue = arrayOfNulls<Any?>(8)
    private var head = 0
    private var tail = 0

    val isEmpty get() = head == tail

    fun poll(): T? {
        if (isEmpty) return null
        val result = queue[head]!!
        queue[head] = null
        head = head.next()
        @Suppress("UNCHECKED_CAST")
        return result as T
    }

    tailrec fun add(element: T) {
        val newTail = tail.next()
        if (newTail == head) {
            resize()
            add(element) // retry with larger size
            return
        }
        queue[tail] = element
        tail = newTail
    }

    private fun resize() {
        var i = head
        var j = 0
        val a = arrayOfNulls<Any?>(queue.size * 2)
        while (i != tail) {
            a[j++] = queue[i]
            i = i.next()
        }
        queue = a
        head = 0
        tail = j
    }

    private fun Int.next(): Int {
        val j = this + 1
        return if (j == queue.size) 0 else j
    }
}
