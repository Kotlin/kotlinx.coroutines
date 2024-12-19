package kotlinx.coroutines.internal

import kotlinx.atomicfu.*

internal actual class LocalAtomicInt actual constructor(value: Int) {

    private val iRef = atomic(value)

    actual fun set(value: Int) {
        iRef.value = value
    }

    actual fun get(): Int = iRef.value

    actual fun decrementAndGet(): Int = iRef.decrementAndGet()
}

internal actual class LocalAtomicRef<V> actual constructor(initialValue: V) {

    private val iRef = atomic(initialValue)

    actual fun get(): V = iRef.value
    actual fun set(value: V) { iRef.value = value }
    actual fun lazySet(value: V) { iRef.lazySet(value) }
    actual fun getAndSet(value: V): V = iRef.getAndSet(value)
    actual fun compareAndSet(expect: V, update: V): Boolean = iRef.compareAndSet(expect, update)
}
