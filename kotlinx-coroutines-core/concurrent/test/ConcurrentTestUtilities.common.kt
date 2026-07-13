package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlin.concurrent.Volatile
import kotlin.random.*

fun randomWait() {
    val n = Random.nextInt(1000)
    if (n < 500) return // no wait 50% of time
    repeat(n) {
        BlackHole.sink *= 3
    }
    // use the BlackHole value somehow, so even if the compiler gets smarter, it won't remove the object
    val sinkValue = if (BlackHole.sink > 16) 1 else 0
    if (n + sinkValue > 900) yieldThread()
}

private object BlackHole {
    @Volatile
    var sink = 1
}

expect inline fun yieldThread()

expect fun currentThreadName(): String

inline fun CloseableCoroutineDispatcher.use(block: (CloseableCoroutineDispatcher) -> Unit) {
    try {
        block(this)
    } finally {
        close()
    }
}
