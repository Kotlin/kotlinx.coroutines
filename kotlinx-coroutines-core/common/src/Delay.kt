/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.time.*

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

    /** @suppress **/
    @Deprecated(
        message = "Deprecated without replacement as an internal method never intended for public use",
        level = DeprecationLevel.ERROR
    ) // Error since 1.6.0
    public suspend fun delay(time: Long) {
        if (time <= 0) return // don't delay
        return suspendCancellableCoroutine { scheduleResumeAfterDelay(time, it) }
    }

    /**
     * Schedules resume of a specified [continuation] after a specified delay [timeMillis].
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
    public fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>)

    /**
     * Schedules invocation of a specified [block] after a specified delay [timeMillis].
     * The resulting [DisposableHandle] can be used to [dispose][DisposableHandle.dispose] of this invocation
     * request if it is not needed anymore.
     */
    public fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        DefaultDelay.invokeOnTimeout(timeMillis, block, context)
}

/**
 * Enhanced [Delay] interface that provides additional diagnostics for [withTimeout].
 * Is going to be removed once there is proper JVM-default support.
 * Then we'll be able put this function into [Delay] without breaking binary compatibility.
 */
@InternalCoroutinesApi
internal interface DelayWithTimeoutDiagnostics : Delay {
    /**
     * Returns a string that explains that the timeout has occurred, and explains what can be done about it.
     */
    fun timeoutMessage(timeout: Duration): String
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
 * Delays coroutine for a given time without blocking a thread and resumes it after a specified time.
 * If the given [timeMillis] is non-positive, this function returns immediately.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
 * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
 *
 * If you want to delay forever (until cancellation), consider using [awaitCancellation] instead.
 *
 * Note that delay can be used in [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * Implementation note: how exactly time is tracked is an implementation detail of [CoroutineDispatcher] in the context.
 * @param timeMillis time in milliseconds.
 */
public suspend fun delay(timeMillis: Long) {
    if (timeMillis <= 0) return // don't delay
    return suspendCancellableCoroutine sc@ { cont: CancellableContinuation<Unit> ->
        // if timeMillis == Long.MAX_VALUE then just wait forever like awaitCancellation, don't schedule.
        if (timeMillis < Long.MAX_VALUE) {
            cont.context.delay.scheduleResumeAfterDelay(timeMillis, cont)
        }
    }
}

/**
 * Delays coroutine for a given [duration] without blocking a thread and resumes it after the specified time.
 * If the given [duration] is non-positive, this function returns immediately.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
 * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
 *
 * If you want to delay forever (until cancellation), consider using [awaitCancellation] instead.
 *
 * Note that delay can be used in [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * Implementation note: how exactly time is tracked is an implementation detail of [CoroutineDispatcher] in the context.
 */
public suspend fun delay(duration: Duration): Unit = delay(duration.toDelayMillis())

/** Returns [Delay] implementation of the given context */
internal val CoroutineContext.delay: Delay get() = get(ContinuationInterceptor) as? Delay ?: DefaultDelay

/**
 * Convert this duration to its millisecond value.
 * Positive durations are coerced at least `1`.
 */
internal fun Duration.toDelayMillis(): Long =
    if (this > Duration.ZERO) inWholeMilliseconds.coerceAtLeast(1) else 0
