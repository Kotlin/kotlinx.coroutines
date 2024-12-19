package kotlinx.coroutines.internal

import kotlin.concurrent.*

/**
 * Atomic array with lock-free reads and synchronized modifications. It logically has an unbounded size,
 * is implicitly filled with nulls, and is resized on updates as needed to grow.
 */
internal class ResizableAtomicArray<T>(initialLength: Int): SynchronizedObject() {
    @Volatile
    private var array = Array(initialLength) { LocalAtomicRef<T?>(null) }

    // for debug output
    public fun currentLength(): Int = array.size

    public operator fun get(index: Int): T? {
        val array = this.array // volatile read
        return if (index < array.size) array[index].get() else null
    }

    // Must not be called concurrently, e.g. always use synchronized(this) to call this function
    fun setSynchronized(index: Int, value: T?) {
        val curArray = this.array
        val curLen = curArray.size
        if (index < curLen) {
            curArray[index].set(value)
            return
        }
        // It would be nice to copy array in batch instead of 1 by 1, but it seems like Java has no API for that
        val newArray = Array((index + 1).coerceAtLeast(2 * curLen)) { LocalAtomicRef<T?>(null) }
        for (i in 0 until curLen) newArray[i].set(curArray[i].get())
        newArray[index].set(value)
        array = newArray // copy done
    }
}
