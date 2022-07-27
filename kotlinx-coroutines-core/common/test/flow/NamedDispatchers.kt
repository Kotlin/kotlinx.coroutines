/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * Test dispatchers that emulate multiplatform context tracking.
 */
public object NamedDispatchers {

    private val stack = ArrayStack()

    public fun name(): String = stack.peek() ?: error("No names on stack")

    public fun nameOr(defaultValue: String): String = stack.peek() ?: defaultValue

    public operator fun invoke(name: String) = named(name)

    private fun named(name: String): CoroutineDispatcher = object : CoroutineDispatcher() {
        override fun dispatch(context: CoroutineContext, block: Runnable) {
            stack.push(name)
            try {
                block.run()
            } finally {
                val last = stack.pop() ?: error("No names on stack")
                require(last == name) { "Inconsistent stack: expected $name, but had $last" }
            }
        }
    }
}

private class ArrayStack {
    private var elements = arrayOfNulls<String>(16)
    private var head = 0

    public fun push(value: String) {
        if (elements.size == head - 1) ensureCapacity()
        elements[head++] = value
    }

    public fun peek(): String? = elements.getOrNull(head - 1)

    public fun pop(): String? {
        if (head == 0) return null
        return elements[--head]
    }

    private fun ensureCapacity() {
        val currentSize = elements.size
        val newCapacity = currentSize shl 1
        val newElements = arrayOfNulls<String>(newCapacity)
        elements.copyInto(
            destination = newElements,
            startIndex = head
        )
        elements.copyInto(
            destination = newElements,
            destinationOffset = elements.size - head,
            endIndex = head
        )
        elements = newElements
    }
}
