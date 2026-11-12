package kotlinx.coroutines.internal

internal expect class CommonThreadLocal<T> {
    fun get(): T
    fun set(value: T)
    fun remove()
}

/**
 * Create a thread-local storage for an object of type [T].
 */
internal expect fun<T> commonThreadLocal(): CommonThreadLocal<T>
