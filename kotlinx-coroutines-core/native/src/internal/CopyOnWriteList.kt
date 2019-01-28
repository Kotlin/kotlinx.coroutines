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
        arraycopy(array, 0, update, 0, index)
        update[index] = element
        arraycopy(array, index, update, index + 1, _size - index + 1)
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
        arraycopy(array, 0, update, 0, index)
        arraycopy(array, index + 1, update, index, n - index - 1)
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
