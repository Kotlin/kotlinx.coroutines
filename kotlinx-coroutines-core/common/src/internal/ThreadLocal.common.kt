package kotlinx.coroutines.internal

internal expect class CommonThreadLocal<T> {
    fun get(): T
    fun set(value: T)
}

/**
 * Create a thread-local storage for an object of type [T].
 *
 * If two different thread-local objects share the same [name], they will not necessarily share the same value,
 * but they may.
 * Therefore, use a unique [name] for each thread-local object.
 */
internal expect fun<T> commonThreadLocal(name: Symbol): CommonThreadLocal<T>
