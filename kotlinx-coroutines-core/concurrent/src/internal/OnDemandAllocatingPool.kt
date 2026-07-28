package kotlinx.coroutines.internal

import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlin.concurrent.atomics.*

/**
 * A thread-safe resource pool.
 *
 * [maxCapacity] is the maximum amount of elements.
 *
 * This is only used in the Native implementation,
 * but is part of the `concurrent` source set in order to test it on the JVM.
 */
@OptIn(ExperimentalAtomicApi::class)
internal class OnDemandAllocatingPool<T>(private val maxCapacity: Int) {
    /**
     * Number of existing elements + isClosed flag in the highest bit.
     * Once the flag is set, the value is guaranteed not to change anymore.
     */
    private val controlState = atomic(0)

    /**
     * Each cell is:
     * - `null` if it was untouched.
     * - `T` if it was created but not yet cleaned up.
     * - `BROKEN` after [close] processes this cell (possibly before it was filled with `T`).
     */
    private val elements = atomicArrayOfNulls<Any?>(maxCapacity)

    /**
     * Returns the upper bound on the number of elements that need to be cleaned up due to the pool being closed.
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
    inline fun allocate(create: (Int) -> T): Boolean {
        controlState.loop { ctl ->
            if (ctl.isClosed()) return false
            if (ctl >= maxCapacity) return true
            if (controlState.compareAndSet(ctl, ctl + 1)) {
                return elements.compareAndSetAt(ctl, null, create(ctl))
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
        return buildList {
            for (i in 0 until elementsExisting) {
                val element = elements.exchangeAt(i, BROKEN)
                if (element != null) {
                    @Suppress("UNCHECKED_CAST")
                    add(element as T)
                }
            }
        }
    }

    // for tests
    internal fun stateRepresentation(): String {
        val ctl = controlState.value
        val elementsStr = (0 until (ctl and IS_CLOSED_MASK.inv())).map { elements.loadAt(it) }.toString()
        val closedStr = if (ctl.isClosed()) "[closed]" else ""
        return elementsStr + closedStr
    }

    override fun toString(): String = "OnDemandAllocatingPool(${stateRepresentation()})"
}

private const val IS_CLOSED_MASK = 1 shl 31
private val BROKEN = Symbol("BROKEN")
