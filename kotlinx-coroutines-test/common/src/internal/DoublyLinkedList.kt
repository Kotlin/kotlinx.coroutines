/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal

internal class DoublyLinkedList<T: Any> {
    var sentinel: Node<T> = Node(null)

    internal class Node<T>(val value: T?) {
        var previous: Node<T>? = null
        var next: Node<T>? = null
    }

    fun add(value: T): Node<T> {
        val oldHead = sentinel.next
        val newHead = Node(value)
        newHead.next = oldHead
        newHead.previous = sentinel
        sentinel.next = newHead
        return newHead
    }

    fun remove(node: Node<T>) {
        val previous = node.previous
        val next = node.next
        previous?.next = next
        next?.previous = previous
    }

    fun toList(): List<T> {
        val result = mutableListOf<T>()
        var current = sentinel.next
        while (current != null) {
            result.add(current.value!!)
            current = current.next
        }
        return result
    }
}
