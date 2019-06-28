/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

@Suppress("UNCHECKED_CAST")
internal class CopyOnWriteList<E>(private var array: Array<Any?> = arrayOfNulls(4)) : AbstractMutableList<E>() {

    private var _size = 0
    override val size: Int get() = _size

    override fun add(element: E): Boolean {
        val newSize = if (_size == array.size) array.size * 2 else  array.size
        val update = array.copyOf(newSize)
        update[_size++] = element
        array = update
        return true
    }

    override fun add(index: Int, element: E) {
        rangeCheck(index)
        val update = arrayOfNulls<Any?>(if (array.size == _size) array.size * 2 else array.size)
        array.copyInto(
            destination = update,
            endIndex = index
        )
        update[index] = element
        array.copyInto(
            destination = update,
            destinationOffset = index + 1,
            startIndex = index,
            endIndex = _size + 1
        )
        array = update
    }

    override fun remove(element: E): Boolean {
        val index = array.indexOf(element as Any)
        if (index == -1) {
            return false
        }

        removeAt(index)
        return true
    }

    override fun removeAt(index: Int): E {
        rangeCheck(index)
        modCount++
        val n = array.size
        val element = array[index]
        val update = arrayOfNulls<Any>(n)
        array.copyInto(
            destination = update,
            endIndex = index
        )
        array.copyInto(
            destination = update,
            destinationOffset = index,
            startIndex = index + 1,
            endIndex = n
        )
        array = update
        --_size
        return element as E
    }

    override fun iterator(): MutableIterator<E> = IteratorImpl(array as Array<E>, size)

    override fun listIterator(): MutableListIterator<E> = throw UnsupportedOperationException("Operation is not supported")

    override fun listIterator(index: Int): MutableListIterator<E> = throw UnsupportedOperationException("Operation is not supported")

    override fun isEmpty(): Boolean = size == 0

    override fun set(index: Int, element: E): E = throw UnsupportedOperationException("Operation is not supported")

    override fun get(index: Int): E = array[rangeCheck(index)]!! as E

    private class IteratorImpl<E>(private var array: Array<E>, private val size: Int) : MutableIterator<E> {

        private var current = 0

        override fun hasNext(): Boolean = current != size

        override fun next(): E {
            if (!hasNext()) {
                throw NoSuchElementException()
            }

            return array[current++]!!
        }

        override fun remove() = throw UnsupportedOperationException("Operation is not supported")
    }

    private fun rangeCheck(index: Int) = index.apply {
        if (index < 0 || index >= _size) {
            throw IndexOutOfBoundsException("index: $index, size: $size")
        }
    }
}
