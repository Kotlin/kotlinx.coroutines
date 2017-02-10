/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.ContinuationInterceptor

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
        val timeout = scheduledExecutor.schedule(ResumeRunnable(cont), time, unit)
        cont.cancelFutureOnCompletion(timeout)
    }
}
