package kotlinx.coroutines.internal

internal actual class LocalAtomicInt actual constructor(private var value: Int) {
    actual fun set(value: Int) {
        this.value = value
    }

    actual fun get(): Int = value

    actual fun decrementAndGet(): Int = --value
}

internal actual class LocalAtomicRef<V> actual constructor(initialValue: V) {

    private var iRef = initialValue

    actual fun get(): V = iRef
    actual fun set(value: V) { iRef = value }
    actual fun lazySet(value: V) { iRef = value }
    actual fun getAndSet(value: V): V = iRef.also { iRef = value }
    actual fun compareAndSet(expect: V, update: V): Boolean = (iRef == expect).also { if (it) iRef = update }
}
