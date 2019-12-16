package kotlinx.coroutines.internal

import kotlinx.coroutines.*


/**
 * CircularArray implementation which will hold the latest of up to `size` elements.
 *
 * After the cache has been filled, all further additions will overwrite the least recent value.
 *
 * @param size the maximum number of elements to store in the array
 */
internal class CircularArray<T>(size: Int) : Iterable<T> {

    private val array: Array<Any?> = arrayOfNulls(size)
    private var count: Int = 0
    private var tail: Int = -1

    /**
     * Adds [item] to the [CircularArray].
     *
     * If the `CircularArray` has not yet been filled,
     * `item` will simply be added to the next available slot.
     *
     * If the `CircularArray` has already been filled,
     * `item` will replace the oldest item already in the array.
     *
     * example:
     * ```
     * val ca = CircularArray<T>(3)
     *
     * ca.add(0)      // ca contents : [0, null, null]
     * ca.add(1)      // ca contents : [0, 1, null]
     * ca.add(2)      // ca contents : [0, 1, 2]
     * // overwrite the oldest value
     * ca.add(3)      // ca contents : [3, 1, 2]
     * ```
     */
    public fun add(item: T) {
        tail = (tail + 1) % array.size
        array[tail] = item
        if (count < array.size) count++
    }

    /**
     * Iterates over the [CircularArray].
     *
     * Order is always first-in-first-out, with the oldest item being used first.
     *
     * example:
     * ```
     * val ca = CircularArray<Int>(3)
     *
     * ca.add(0)            // ca contents : [0, null, null]
     * ca.add(1)            // ca contents : [0, 1, null]
     * ca.add(2)            // ca contents : [0, 1, 2]
     * // overwrite the oldest value
     * ca.add(3)            // ca contents : [3, 1, 2]
     *
     * ca.forEach { ... }   // order : [1, 2, 3]
     * ```
     */
    public override fun iterator(): Iterator<T> = object : Iterator<T> {
        private val arraySnapshot = array.copyOf()
        private val tailSnapshot = tail

        private var _index = 0

        private val head: Int
            get() = when (count) {
                arraySnapshot.size -> (tailSnapshot + 1) % count
                else -> 0
            }

        @Suppress("UNCHECKED_CAST")
        private fun get(index: Int): T = when (count) {
            arraySnapshot.size -> arraySnapshot[(head + index) % arraySnapshot.size] as T
            else -> arraySnapshot[index] as T
        }

        override fun hasNext(): Boolean = _index < count
        override fun next(): T = get(_index++)

    }

    public override fun toString(): String = "$classSimpleName[array=${contentToString()}]"

    private fun contentToString(): String = joinToString { "$it" }
}
