package kotlinx.coroutines.internal

internal actual class LocalAtomicInt actual constructor(private var value: Int) {
    actual fun set(value: Int) {
        this.value = value
    }

    actual fun get(): Int = value

    actual fun decrementAndGet(): Int = --value
}
