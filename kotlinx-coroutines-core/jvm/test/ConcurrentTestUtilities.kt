package kotlinx.coroutines.exceptions

actual inline fun yieldThread() { Thread.yield() }

actual fun currentThreadName(): String = Thread.currentThread().name
