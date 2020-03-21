/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

/**
 * Analogue of java.util.concurrent.CopyOnWriteArrayList for JS.
 * Even though JS has no real concurrency, [CopyOnWriteList] is essential to manage any kinds
 * of callbacks or continuations.
 *
 * Implementation note: most of the methods fallbacks to [AbstractMutableList] (thus inefficient for CoW pattern)
 * and some methods are unsupported, because currently they are not required for this class consumers.
 */
internal class CopyOnWriteList<E>(private var array: Array<E> = emptyArray()) : AbstractMutableList<E>() {

    override val size: Int get() = array.size

    override fun add(element: E): Boolean {
        val copy = array.asDynamic().slice()
        copy.push(element)
        array = copy as Array<E>
        return true
    }

    override fun add(index: Int, element: E) {
        val copy = array.asDynamic().slice()
        copy.splice(insertionRangeCheck(index), 0, element)
        array = copy as Array<E>
    }

    override fun remove(element: E): Boolean {
        for (index in array.indices) {
            if (array[index] == element) {
                val copy = array.asDynamic().slice()
                copy.splice(index, 1)
                array = copy as Array<E>
                return true
            }
        }

        return false
    }

    override fun removeAt(index: Int): E {
        rangeCheck(index)
        val copy = array.asDynamic().slice()
        val result = if (index == lastIndex) {
            copy.pop()
        } else {
            copy.splice(index, 1)[0]
        }

        array = copy as Array<E>
        return result as E
    }

    override fun iterator(): MutableIterator<E> = IteratorImpl(array)

    override fun listIterator(): MutableListIterator<E> = throw UnsupportedOperationException("Operation is not supported")

    override fun listIterator(index: Int): MutableListIterator<E> = throw UnsupportedOperationException("Operation is not supported")

    override fun isEmpty(): Boolean = size == 0

    override fun set(index: Int, element: E): E = throw UnsupportedOperationException("Operation is not supported")

    override fun get(index: Int): E = array[rangeCheck(index)]

    private class IteratorImpl<E>(private var array: Array<E>) : MutableIterator<E> {

        private var current = 0

        override fun hasNext(): Boolean = current != array.size

        override fun next(): E {
            if (!hasNext()) {
                throw NoSuchElementException()
            }

            return array[current++]
        }

        override fun remove() = throw UnsupportedOperationException("Operation is not supported")
    }

    private fun insertionRangeCheck(index: Int) {
        if (index < 0 || index > size) {
            throw IndexOutOfBoundsException("index: $index, size: $size")
        }
    }

    private fun rangeCheck(index: Int) = index.apply {
        if (index < 0 || index >= size) {
            throw IndexOutOfBoundsException("index: $index, size: $size")
        }
    }
}
