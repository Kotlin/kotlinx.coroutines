/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*

/**
 * A thread-safe resource pool.
 *
 * [maxCapacity] is the maximum amount of elements.
 * [create] is the function that creates a new element.
 *
 * This is only used in the Native implementation,
 * but is part of the `concurrent` source set in order to test it on the JVM.
 */
internal class OnDemandAllocatingPool<T>(
    private val maxCapacity: Int,
    private val create: (Int) -> T
) {
    /**
     * Number of existing elements + isClosed flag in the highest bit.
     * Once the flag is set, the value is guaranteed not to change anymore.
     */
    private val controlState = atomic(0)
    private val elements = atomicArrayOfNulls<T>(maxCapacity)

    /**
     * Returns the number of elements that need to be cleaned up due to the pool being closed.
     */
    @Suppress("NOTHING_TO_INLINE")
    private inline fun tryForbidNewElements(): Int {
        controlState.loop {
            if (it.isClosed()) return 0 // already closed
            if (controlState.compareAndSet(it, it or IS_CLOSED_MASK)) return it
        }
    }

    @Suppress("NOTHING_TO_INLINE")
    private inline fun Int.isClosed(): Boolean = this and IS_CLOSED_MASK != 0

    /**
     * Request that a new element is created.
     *
     * Returns `false` if the pool is closed.
     *
     * Note that it will still return `true` even if an element was not created due to reaching [maxCapacity].
     *
     * Rethrows the exceptions thrown from [create]. In this case, this operation has no effect.
     */
    fun allocate(): Boolean {
        controlState.loop { ctl ->
            if (ctl.isClosed()) return false
            if (ctl >= maxCapacity) return true
            if (controlState.compareAndSet(ctl, ctl + 1)) {
                elements[ctl].value = create(ctl)
                return true
            }
        }
    }

    /**
     * Close the pool.
     *
     * This will prevent any new elements from being created.
     * All the elements present in the pool will be returned.
     *
     * The function is thread-safe.
     *
     * [close] can be called multiple times, but only a single call will return a non-empty list.
     * This is due to the elements being cleaned out from the pool on the first invocation to avoid memory leaks,
     * and no new elements being created after.
     */
    fun close(): List<T> {
        val elementsExisting = tryForbidNewElements()
        return (0 until elementsExisting).map { i ->
            // we wait for the element to be created, because we know that eventually it is going to be there
            loop {
                val element = elements[i].getAndSet(null)
                if (element != null) {
                    return@map element
                }
            }
        }
    }

    // for tests
    internal fun stateRepresentation(): String {
        val ctl = controlState.value
        val elementsStr = (0 until (ctl and IS_CLOSED_MASK.inv())).map { elements[it].value }.toString()
        val closedStr = if (ctl.isClosed()) "[closed]" else ""
        return elementsStr + closedStr
    }

    override fun toString(): String = "OnDemandAllocatingPool(${stateRepresentation()})"
}

// KT-25023
private inline fun loop(block: () -> Unit): Nothing {
    while (true) {
        block()
    }
}

private const val IS_CLOSED_MASK = 1 shl 31
