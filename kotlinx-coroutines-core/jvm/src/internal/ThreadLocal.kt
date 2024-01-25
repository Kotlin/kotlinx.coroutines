package kotlinx.coroutines.internal

import java.lang.ThreadLocal

@Suppress("ACTUAL_WITHOUT_EXPECT") // internal visibility
internal actual typealias CommonThreadLocal<T> = ThreadLocal<T>

internal actual fun<T> commonThreadLocal(name: Symbol): CommonThreadLocal<T> = ThreadLocal()
