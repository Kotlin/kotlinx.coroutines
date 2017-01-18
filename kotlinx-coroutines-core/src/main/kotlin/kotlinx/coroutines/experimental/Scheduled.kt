package kotlinx.coroutines.experimental

import java.util.concurrent.Executors
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.TimeUnit
import kotlin.coroutines.startCoroutine

internal val scheduledExecutor by lazy<ScheduledExecutorService> {
    Executors.newScheduledThreadPool(1) { r ->
        Thread(r, "kotlinx.coroutines.ScheduledExecutor").apply { isDaemon = true }
    }
}

/**
 * Runs a given suspending block of code inside a coroutine with a specified timeout and throws
 * [CancellationException] if timeout was exceeded.
 */
suspend fun <T> withTimeout(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS, block: suspend () -> T): T {
    require(time >= 0) { "Timeout time $time cannot be negative" }
    if (time <= 0L) throw CancellationException("Timed out immediately")
    return suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
        // schedule cancellation of this continuation on time
        val timeout = scheduledExecutor.schedule({
            // create an exception with a specific text
            cont.cancel(CancellationException("Timed out waiting for $time $unit"))
        }, time, unit)
        cont.cancelFutureOnCompletion(timeout)
        // restart block in a separate coroutine using cancellable context of this continuation,
        block.startCoroutine(cont)
    }
}
