package kotlinx.coroutines.testing

import kotlinx.atomicfu.locks.*
import kotlin.time.*

expect fun assertTrueJvm(value: Boolean)

@OptIn(ExperimentalThreadBlockingApi::class)
fun concurrentSleep(duration: Duration) {
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

expect fun runThread(
    name: String? = null, block: () -> Unit
): ConcurrentThread

expect class ConcurrentThread(
    name: String? = null, block: () -> Unit
) {
    fun start()
    fun join()
}
