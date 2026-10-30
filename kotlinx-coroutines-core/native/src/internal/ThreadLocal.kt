package kotlinx.coroutines.internal

import kotlin.native.concurrent.ThreadLocal

internal actual class CommonThreadLocal<T>(private val reference: Any) {
    @Suppress("UNCHECKED_CAST")
    actual fun get(): T = Storage[reference] as T
    actual fun set(value: T) { Storage[reference] = value }
    actual fun remove() { Storage.remove(reference) }
}

internal actual fun <T> commonThreadLocal(): CommonThreadLocal<T> = CommonThreadLocal(Any())

@ThreadLocal
private object Storage: MutableMap<Any, Any?> by mutableMapOf()
