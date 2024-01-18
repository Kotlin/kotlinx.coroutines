package kotlinx.coroutines.internal

import kotlin.native.concurrent.ThreadLocal

internal actual class CommonThreadLocal<T>(private val name: Symbol) {
    @Suppress("UNCHECKED_CAST")
    actual fun get(): T = Storage[name] as T
    actual fun set(value: T) { Storage[name] = value }
}

internal actual fun <T> commonThreadLocal(name: Symbol): CommonThreadLocal<T> = CommonThreadLocal(name)

@ThreadLocal
private object Storage: MutableMap<Symbol, Any?> by mutableMapOf()
