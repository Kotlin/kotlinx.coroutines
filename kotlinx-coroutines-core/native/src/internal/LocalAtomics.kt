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
