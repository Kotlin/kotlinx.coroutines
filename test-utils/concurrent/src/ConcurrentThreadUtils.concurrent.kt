package kotlinx.coroutines.testing

import kotlinx.atomicfu.locks.*
import kotlinx.coroutines.*
import kotlin.time.*

expect fun assertTrueJvm(value: Boolean)

@OptIn(ExperimentalThreadBlockingApi::class)
fun threadSleep(duration: Duration) {
    if (duration <= Duration.ZERO) return
    val start = TimeSource.Monotonic.markNow()
    ParkingSupport.park(duration)
    while (true) {
        val elapsed = start.elapsedNow()
        val remaining = duration - elapsed
        if (remaining <= Duration.ZERO) return
        ParkingSupport.park(remaining)
    }
}


expect class ConcurrentThread(
    block: Runnable, name: String?
) {
    fun start()
    fun join()
}

fun ConcurrentThread(name: String?, block: () -> Unit) = ConcurrentThread({ block() }, name)
