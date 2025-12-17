package kotlinx.coroutines.exceptions

@Suppress("NOTHING_TO_INLINE")
actual inline fun yieldThread() { Thread.yield() }

actual fun currentThreadName(): String = Thread.currentThread().name
