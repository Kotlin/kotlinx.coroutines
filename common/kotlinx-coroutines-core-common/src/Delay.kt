/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.selects.*
import kotlinx.coroutines.timeunit.*
import kotlin.coroutines.*

/**
 * This dispatcher _feature_ is implemented by [CoroutineDispatcher] implementations that natively support
 * scheduled execution of tasks.
 *
 * Implementation of this interface affects operation of
 * [delay][kotlinx.coroutines.delay] and [withTimeout] functions.
 */
public interface Delay {
    /**
     * Delays coroutine for a given time without blocking a thread and resumes it after a specified time.
     * This suspending function is cancellable.
     * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
     * immediately resumes with [CancellationException].
     */
    suspend fun delay(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS) {
        if (time <= 0) return // don't delay
        return suspendCancellableCoroutine { scheduleResumeAfterDelay(time, unit, it) }
    }

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
    fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>)

    /**
     * Schedules invocation of a specified [block] after a specified delay [time].
     * The resulting [DisposableHandle] can be used to [dispose][DisposableHandle.dispose] of this invocation
     * request if it is not needed anymore.
     *
     * This implementation uses a built-in single-threaded scheduled executor service.
     */
    fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle =
        DefaultDelay.invokeOnTimeout(time, unit, block)
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
 * @param time time in milliseconds.
 */
public suspend fun delay(time: Int) =
    delay(time.toLong(), TimeUnit.MILLISECONDS)

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
 */
public suspend fun delay(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS) {
    if (time <= 0) return // don't delay
    return suspendCancellableCoroutine sc@ { cont: CancellableContinuation<Unit> ->
        cont.context.delay.scheduleResumeAfterDelay(time, unit, cont)
    }
}

/** Returns [Delay] implementation of the given context */
internal val CoroutineContext.delay: Delay get() = get(ContinuationInterceptor) as? Delay ?: DefaultDelay
