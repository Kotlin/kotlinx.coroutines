/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

internal class ArrayQueue<T : Any> {
    public val isEmpty: Boolean get() = head == tail

    private var elements = arrayOfNulls<Any>(16)
    private var head = 0
    private var tail = 0

    public fun addLast(element: T) {
        elements[tail] = element
        tail = (tail + 1) and elements.size - 1
        if (tail == head) ensureCapacity()
    }

    @Suppress("UNCHECKED_CAST")
    public fun removeFirst(): T {
        require(head != tail) { "Queue is empty" }
        val element = elements[head]
        elements[head] = null
        head = (head + 1) and elements.size - 1
        return element!! as T
    }

    public fun clear() {
        head = 0
        tail = 0
        elements = arrayOfNulls(elements.size)
    }

    private fun ensureCapacity() {
        val currentSize = elements.size
        val newCapacity = currentSize shl 1
        val newElements = arrayOfNulls<Any>(newCapacity)
        val remaining = elements.size - head
        arraycopy(elements, head, newElements, 0, remaining)
        arraycopy(elements, 0, newElements, remaining, head)
        elements = newElements
        head = 0
        tail = currentSize
    }
}
