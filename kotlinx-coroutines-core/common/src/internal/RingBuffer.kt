package kotlinx.coroutines.internal

internal class RingBuffer<T>(val capacity: Int) : AbstractList<T>(), RandomAccess {
    init {
        require(capacity >= 0) { "ring buffer capacity should not be negative but it is $capacity" }
    }

    private val buffer = arrayOfNulls<Any?>(capacity)
    private var startIndex: Int = 0

    override var size: Int = 0
        private set

    override fun get(index: Int): T {
        require(index in 0 until size) { "Index out of bounds: $index" }
        @Suppress("UNCHECKED_CAST")
        return buffer[startIndex.forward(index)] as T
    }

    fun isFull() = size == capacity

    override fun iterator(): Iterator<T> = object : AbstractIterator<T>() {
        private var count = size
        private var index = startIndex

        override fun computeNext() {
            if (count == 0) {
                done()
            } else {
                @Suppress("UNCHECKED_CAST")
                setNext(buffer[index] as T)
                index = index.forward(1)
                count--
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    override fun <T> toArray(array: Array<T>): Array<T> {
        val result: Array<T?> =
                if (array.size < this.size) array.copyOf(this.size) else array as Array<T?>

        val size = this.size

        var widx = 0
        var idx = startIndex

        while (widx < size && idx < capacity) {
            result[widx] = buffer[idx] as T
            widx++
            idx++
        }

        idx = 0
        while (widx < size) {
            result[widx] = buffer[idx] as T
            widx++
            idx++
        }
        if (result.size > this.size) result[this.size] = null

        return result as Array<T>
    }

    override fun toArray(): Array<Any?> {
        return toArray(arrayOfNulls(size))
    }

    /**
     * Add [element] to the buffer or fail with [IllegalStateException] if no free space available in the buffer
     */
    fun add(element: T) {
        check(!isFull()) { "Ring buffer is full" }

        buffer[startIndex.forward(size)] = element
        size++
    }

    /**
     * Removes [n] first elements from the buffer or fails with [IllegalArgumentException] if not enough elements in the buffer to remove
     */
    fun removeFirst(n: Int) {
        require(n >= 0) { "n shouldn't be negative but it is $n" }
        require(n <= size) { "n shouldn't be greater than the buffer size: n = $n, size = $size" }

        if (n > 0) {
            val start = startIndex
            val end = start.forward(n)

            if (start > end) {
                buffer.fill(null, start, capacity)
                buffer.fill(null, 0, end)
            } else {
                buffer.fill(null, start, end)
            }

            startIndex = end
            size -= n
        }
    }


    @Suppress("NOTHING_TO_INLINE")
    private inline fun Int.forward(n: Int): Int = (this + n) % capacity
}