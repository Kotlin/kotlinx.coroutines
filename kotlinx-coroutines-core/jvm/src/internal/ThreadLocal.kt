package kotlinx.coroutines.internal

import java.lang.ThreadLocal

internal actual typealias CommonThreadLocal<T> = ThreadLocal<T>

internal actual fun<T> commonThreadLocal(): CommonThreadLocal<T> = ThreadLocal()
