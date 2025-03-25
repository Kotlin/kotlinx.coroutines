package kotlinx.coroutines.testing

import kotlinx.atomicfu.atomic
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.withTimeoutOrNull
import kotlin.time.Duration

actual class CountDownLatch actual constructor(initial: Int) {
    private val counter = atomic(initial)
    private val wakeUpSignal = Channel<Unit>(Channel.CONFLATED)

    actual fun countDown() {
        if (counter.decrementAndGet() <= 0) {
            wakeUpSignal.trySend(Unit)
        }
    }

    actual fun await() {
        if (counter.value > 0) {
            runBlocking {
                wakeUpSignal.receive()
                wakeUpSignal.trySend(Unit)
            }
        }
    }

    internal fun awaitTimingOut(timeout: Duration): Boolean = counter.value > 0 || runBlocking {
        val result = withTimeoutOrNull(timeout) {
            wakeUpSignal.receive()
        }
        if (result == null) {
            false
        } else {
            wakeUpSignal.trySend(Unit)
            true
        }
    }
}

actual fun CountDownLatch.await(timeout: Duration) = awaitTimingOut(timeout)
