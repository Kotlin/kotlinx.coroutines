package kotlinx.coroutines.experimental

import java.util.concurrent.TimeUnit
import kotlin.coroutines.ContinuationInterceptor

/**
 * This dispatcher _feature_ is implemented by [CoroutineDispatcher] implementations that natively support
 * non-blocking [delay] function.
 */
public interface Delay {
    /**
     * Delays coroutine for a given time without blocking a thread and resumes it after a specified time.
     * This suspending function is cancellable.
     * If the [Job] of the current coroutine is completed while this suspending function is suspended, this function
     * immediately resumes with [CancellationException].
     */
    suspend fun delay(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS) {
        require(time >= 0) { "Delay time $time cannot be negative" }
        if (time <= 0) return // don't delay
        return suspendCancellableCoroutine { scheduleResumeAfterDelay(time, unit, it) }
    }

    /**
     * Schedules resume of a specified [continuation] after a specified delay [time].
     */
    fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>)
}

/**
 * Delays coroutine for a given time without blocking a thread and resumes it after a specified time.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is completed while this suspending function is suspended, this function
 * immediately resumes with [CancellationException].
 *
 * This function delegates to [Delay] implementation of the context [CoroutineDispatcher] if possible,
 * otherwise it resumes using a built-in single-threaded scheduled executor service.
 */
suspend fun delay(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS) {
    require(time >= 0) { "Delay time $time cannot be negative" }
    if (time <= 0) return // don't delay
    return suspendCancellableCoroutine sc@ { cont: CancellableContinuation<Unit> ->
        (cont.context[ContinuationInterceptor] as? Delay)?.apply {
            scheduleResumeAfterDelay(time, unit, cont)
            return@sc
        }
        val timeout = scheduledExecutor.schedule({ cont.resume(Unit) }, time, unit)
        cont.cancelFutureOnCompletion(timeout)
    }
}
