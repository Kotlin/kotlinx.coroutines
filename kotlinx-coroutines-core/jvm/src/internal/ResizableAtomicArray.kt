/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import java.util.concurrent.atomic.*

/**
 * Atomic array with lock-free reads and synchronized modifications. It logically has an unbounded size,
 * is implicitly filled with nulls, and is resized on updates as needed to grow.
 */
internal class ResizableAtomicArray<T>(initialLength: Int) {
    @Volatile
    private var array = AtomicReferenceArray<T>(initialLength)

    // for debug output
    public fun currentLength(): Int = array.length()

    public operator fun get(index: Int): T? {
        val array = this.array // volatile read
        return if (index < array.length()) array[index] else null
    }

    // Must not be called concurrently, e.g. always use synchronized(this) to call this function
    fun setSynchronized(index: Int, value: T?) {
        val curArray = this.array
        val curLen = curArray.length()
        if (index < curLen) {
            curArray[index] = value
        } else {
            val newArray = AtomicReferenceArray<T>((index + 1).coerceAtLeast(2 * curLen))
            for (i in 0 until curLen) newArray[i] = curArray[i]
            newArray[index] = value
            array = newArray // copy done
        }
    }
}
