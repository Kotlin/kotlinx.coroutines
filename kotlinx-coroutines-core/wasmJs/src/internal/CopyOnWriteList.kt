package kotlinx.coroutines.internal

@Suppress("UNCHECKED_CAST")
internal class CopyOnWriteList<E> : AbstractMutableList<E>() {
    private var array: Array<Any?> = arrayOfNulls<Any?>(0)

    override val size: Int
        get() = array.size

    override fun add(element: E): Boolean {
        val n = size
        val update = array.copyOf(n + 1)
        update[n] = element
        array = update
        return true
    }

    override fun add(index: Int, element: E) {
        rangeCheck(index)
        val n = size
        val update = arrayOfNulls<Any?>(n + 1)
        array.copyInto(destination = update, endIndex = index)
        update[index] = element
        array.copyInto(destination = update, destinationOffset = index + 1, startIndex = index, endIndex = n + 1)
        array = update
    }

    override fun remove(element: E): Boolean {
        val index = array.indexOf(element as Any)
        if (index == -1) return false
        removeAt(index)
        return true
    }

    override fun removeAt(index: Int): E {
        rangeCheck(index)
        val n = size
        val element = array[index]
        val update = arrayOfNulls<Any>(n - 1)
        array.copyInto(destination = update, endIndex = index)
        array.copyInto(destination = update, destinationOffset = index, startIndex = index + 1, endIndex = n)
        array = update
        return element as E
    }

    override fun iterator(): MutableIterator<E> = IteratorImpl(array as Array<E>)
    override fun listIterator(): MutableListIterator<E> = throw UnsupportedOperationException("Operation is not supported")
    override fun listIterator(index: Int): MutableListIterator<E> = throw UnsupportedOperationException("Operation is not supported")
    override fun isEmpty(): Boolean = size == 0
    override fun set(index: Int, element: E): E = throw UnsupportedOperationException("Operation is not supported")
    override fun get(index: Int): E = array[rangeCheck(index)] as E

    private class IteratorImpl<E>(private val array: Array<E>) : MutableIterator<E> {
        private var current = 0

        override fun hasNext(): Boolean = current != array.size

        override fun next(): E {
            if (!hasNext()) throw NoSuchElementException()
            return array[current++]
        }

        override fun remove() = throw UnsupportedOperationException("Operation is not supported")
    }

    private fun rangeCheck(index: Int) = index.apply {
        if (index < 0 || index >= size) throw IndexOutOfBoundsException("index: $index, size: $size")
    }
}
