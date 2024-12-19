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

internal expect class LocalAtomicRef<V>(initialValue: V) {
    fun get(): V
    fun set(value: V)
    fun lazySet(value: V)
    fun getAndSet(value: V): V
    fun compareAndSet(expect: V, update: V): Boolean
}
