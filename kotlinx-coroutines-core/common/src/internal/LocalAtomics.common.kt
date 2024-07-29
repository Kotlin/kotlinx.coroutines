package kotlinx.coroutines.internal

/*
 * These are atomics that are used as local variables
 * where atomicfu doesn't support its tranformations.
 *
 * Have `Local` prefix to avoid AFU clashes during star-imports
 *
 * TODO: remove after https://youtrack.jetbrains.com/issue/KT-62423/
 */
internal expect class LocalAtomicInt(value: Int) {
    fun get(): Int
    fun set(value: Int)
    fun decrementAndGet(): Int
}
