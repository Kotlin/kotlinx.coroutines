/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.selects.*
import kotlinx.coroutines.experimental.timeunit.*
import kotlin.coroutines.experimental.*

/**
 * This dispatcher _feature_ is implemented by [CoroutineDispatcher] implementations that natively support
 * scheduled execution of tasks.
 *
 * Implementation of this interface affects operation of
 * [delay][kotlinx.coroutines.experimental.delay] and [withTimeout] functions.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi // todo: Remove references from other docs
public interface Delay {
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "binary compatibility")
    suspend fun delay(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS) = delay(time.convertToMillis(unit))

    /**
     * Delays coroutine for a given time without blocking a thread and resumes it after a specified time.
     * This suspending function is cancellable.
     * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
     * immediately resumes with [CancellationException].
     */
    suspend fun delay(time: Long) {
        if (time <= 0) return // don't delay
        return suspendCancellableCoroutine { scheduleResumeAfterDelay(time, it) }
    }

    @Deprecated(level = DeprecationLevel.HIDDEN, message = "binary compatibility")
    fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) =
        scheduleResumeAfterDelay(time.convertToMillis(unit), continuation)

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
     * with(continuation) { resumeUndispatched(Unit) }
     * ```
     */
    fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>)

    @Deprecated(level = DeprecationLevel.HIDDEN, message = "binary compatibility")
    fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle =
        DefaultDelay.invokeOnTimeout(time.convertToMillis(unit), block)

    /**
     * Schedules invocation of a specified [block] after a specified delay [timeMillis].
     * The resulting [DisposableHandle] can be used to [dispose][DisposableHandle.dispose] of this invocation
     * request if it is not needed anymore.
     *
     * This implementation uses a built-in single-threaded scheduled executor service.
     */
    fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle =
        DefaultDelay.invokeOnTimeout(timeMillis, block)
}

@Deprecated(level = DeprecationLevel.HIDDEN, message = "binary compatibility")
public suspend fun delay(timeMillis: Int) =
    delay(timeMillis.toLong(), TimeUnit.MILLISECONDS)

/**
 * Delays coroutine for a given time without blocking a thread and resumes it after a specified time.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * Note, that delay can be used in [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * This function delegates to [Delay.scheduleResumeAfterDelay] if the context [CoroutineDispatcher]
 * implements [Delay] interface, otherwise it resumes using a built-in single-threaded scheduled executor service.
 *
 * @param timeMillis time in milliseconds.
 */
public suspend fun delay(timeMillis: Long) {
    if (timeMillis <= 0) return // don't delay
    return suspendCancellableCoroutine sc@ { cont: CancellableContinuation<Unit> ->
        cont.context.delay.scheduleResumeAfterDelay(timeMillis, cont)
    }
}

/**
 * Delays coroutine for a given time without blocking a thread and resumes it after a specified time.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * Note, that delay can be used in [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * This function delegates to [Delay.scheduleResumeAfterDelay] if the context [CoroutineDispatcher]
 * implements [Delay] interface, otherwise it resumes using a built-in single-threaded scheduled executor service.
 *
 * @param time time in the specified [unit].
 * @param unit time unit.
 *
 * @suppress **Deprecated**: Replace with `delay(unit.toMillis(time))`
 */
// todo: review usage in Guides and samples
@Deprecated(
    message = "Replace with delay(unit.toMillis(time))",
    replaceWith = ReplaceWith("delay(unit.toMillis(time))")
)
public suspend fun delay(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS) =
    delay(time.convertToMillis(unit))

internal fun Long.convertToMillis(unit: TimeUnit): Long {
    val result = unit.toMillis(this)
    return when {
        result != 0L -> result
        this > 0 -> 1L
        else -> 0L
    }
}

/** Returns [Delay] implementation of the given context */
internal val CoroutineContext.delay: Delay get() = get(ContinuationInterceptor) as? Delay ?: DefaultDelay
