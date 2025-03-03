package kotlinx.coroutines.internal

internal actual class CommonThreadLocal<T> {
    private var value: T? = null
    @Suppress("UNCHECKED_CAST")
    actual fun get(): T = value as T
    actual fun set(value: T) { this.value = value }
    actual fun remove() { value = null }
}

internal actual fun<T> commonThreadLocal(name: Symbol): CommonThreadLocal<T> = CommonThreadLocal()