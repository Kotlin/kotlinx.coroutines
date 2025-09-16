package kotlinx.coroutines

import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.time.*
import kotlin.time.Duration.Companion.nanoseconds
import kotlin.time.Duration.Companion.milliseconds

/**
 * This dispatcher _feature_ is implemented by [CoroutineDispatcher] implementations that natively support
 * scheduled execution of tasks.
 *
 * Implementation of this interface affects operation of
 * [delay][kotlinx.coroutines.delay] and [withTimeout] functions.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public interface Delay {
    /**
     * Schedules resume of a specified [continuation] after a specified delay [time].
     *
     * Continuation **must be scheduled** to resume even if it is already cancelled, because a cancellation is just
     * an exception that the coroutine that used `delay` might wanted to catch and process. It might
     * need to close some resources in its `finally` blocks, for example.
     *
     * This implementation is supposed to use dispatcher's native ability for scheduled execution in its thread(s).
     * In order to avoid an extra delay of execution, the following code shall be used to resume this
     * [continuation] when the code is already executing in the appropriate thread:
     *
     * ```kotlin
     * with(continuation) { resumeUndispatchedWith(Unit) }
     * ```
     */
    public fun scheduleResumeAfterDelay(time: Duration, continuation: CancellableContinuation<Unit>)

    /**
     * Schedules invocation of a specified [block] after a specified delay [timeout].
     * The resulting [DisposableHandle] can be used to [dispose][DisposableHandle.dispose] of this invocation
     * request if it is not needed anymore.
     */
    public fun invokeOnTimeout(timeout: Duration, block: Runnable, context: CoroutineContext): DisposableHandle =
        DefaultDelay.invokeOnTimeout(timeout, block, context)

    /**
     * Returns a string that explains that the timeout has occurred, and explains what can be done about it.
     */
    public fun timeoutMessage(timeout: Duration): String = "Timed out waiting for $timeout"
}

/**
 * Suspends until cancellation, in which case it will throw a [CancellationException].
 *
 * This function returns [Nothing], so it can be used in any coroutine,
 * regardless of the required return type.
 *
 * Usage example in callback adapting code:
 *
 * ```kotlin
 * fun currentTemperature(): Flow<Temperature> = callbackFlow {
 *     val callback = SensorCallback { degreesCelsius: Double ->
 *         trySend(Temperature.celsius(degreesCelsius))
 *     }
 *     try {
 *         registerSensorCallback(callback)
 *         awaitCancellation() // Suspends to keep getting updates until cancellation.
 *     } finally {
 *         unregisterSensorCallback(callback)
 *     }
 * }
 * ```
 *
 * Usage example in (non declarative) UI code:
 *
 * ```kotlin
 * suspend fun showStuffUntilCancelled(content: Stuff): Nothing {
 *     someSubView.text = content.title
 *     anotherSubView.text = content.description
 *     someView.visibleInScope {
 *         awaitCancellation() // Suspends so the view stays visible.
 *     }
 * }
 * ```
 */
public suspend fun awaitCancellation(): Nothing = suspendCancellableCoroutine {}

/**
 * Delays coroutine for at least the given [duration] without blocking a thread and resumes it after the specified time.
 * If the given [duration] is non-positive, this function returns immediately.
 *
 * This suspending function is cancellable: if the [Job] of the current coroutine is cancelled while this
 * suspending function is waiting, this function immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**: even if this function is ready to return the result, but was cancelled
 * while suspended, [CancellationException] will be thrown. See [suspendCancellableCoroutine] for low-level details.
 *
 * If you want to delay forever (until cancellation), consider using [awaitCancellation] instead.
 *
 * Note that delay can be used in [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * Implementation note: how exactly time is tracked is an implementation detail of [CoroutineDispatcher] in the context.
 */
public suspend fun delay(duration: Duration) {
    if (duration <= Duration.ZERO) return // don't delay
    return suspendCancellableCoroutine sc@ { cont: CancellableContinuation<Unit> ->
        // instead of actually waiting for an infinite time, just wait forever like awaitCancellation, don't schedule.
        if (duration.isFinite()) {
            cont.context.delay.scheduleResumeAfterDelay(duration, cont)
        }
    }
}

/**
 * Delays coroutine for at least the given time without blocking a thread and resumes it after a specified time.
 * If the given [timeMillis] is non-positive, this function returns immediately.
 *
 * This suspending function is cancellable: if the [Job] of the current coroutine is cancelled while this
 * suspending function is waiting, this function immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**: even if this function is ready to return the result, but was cancelled
 * while suspended, [CancellationException] will be thrown. See [suspendCancellableCoroutine] for low-level details.
 *
 * If you want to delay forever (until cancellation), consider using [awaitCancellation] instead.
 *
 * Note that delay can be used in [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * Implementation note: how exactly time is tracked is an implementation detail of [CoroutineDispatcher] in the context.
 * @param timeMillis time in milliseconds.
 */
public suspend fun delay(timeMillis: Long) {
    delay(timeMillis.milliseconds)
}

/** Returns [Delay] implementation of the given context */
internal val CoroutineContext.delay: Delay get() = get(ContinuationInterceptor) as? Delay ?: DefaultDelay

/**
 * Convert this duration to its millisecond value. Durations which have a nanosecond component less than
 * a single millisecond will be rounded up to the next largest millisecond.
 */
@PublishedApi
internal fun Duration.toDelayMillis(): Long = when (isPositive()) {
    true -> plus(999_999L.nanoseconds).inWholeMilliseconds
    false -> 0L
}
