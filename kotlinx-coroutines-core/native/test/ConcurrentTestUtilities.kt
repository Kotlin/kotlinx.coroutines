package kotlinx.coroutines.exceptions

import platform.posix.*
import kotlin.native.concurrent.*

@Suppress("NOTHING_TO_INLINE")
actual inline fun yieldThread() { sched_yield() }

actual fun currentThreadName(): String = Worker.current.name
