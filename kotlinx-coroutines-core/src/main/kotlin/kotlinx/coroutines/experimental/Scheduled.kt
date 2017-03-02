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

import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.ScheduledThreadPoolExecutor
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.startCoroutine

private val KEEP_ALIVE = java.lang.Long.getLong("kotlinx.coroutines.ScheduledExecutor.keepAlive", 1000L)

@Volatile
private var _scheduledExecutor: ScheduledExecutorService? = null

internal val scheduledExecutor: ScheduledExecutorService get() =
    _scheduledExecutor ?: getOrCreateScheduledExecutorSync()

@Synchronized
private fun getOrCreateScheduledExecutorSync(): ScheduledExecutorService =
    _scheduledExecutor ?: ScheduledThreadPoolExecutor(1) { r ->
        Thread(r, "kotlinx.coroutines.ScheduledExecutor").apply { isDaemon = true }
    }.apply {
        setKeepAliveTime(KEEP_ALIVE, TimeUnit.MILLISECONDS)
        allowCoreThreadTimeOut(true)
        executeExistingDelayedTasksAfterShutdownPolicy = false
        // "setRemoveOnCancelPolicy" is available only since JDK7, so try it via reflection
        try {
            val m = this::class.java.getMethod("setRemoveOnCancelPolicy", Boolean::class.javaPrimitiveType)
            m.invoke(this, true)
        } catch (ex: Throwable) { /* ignore */ }
        _scheduledExecutor = this
    }

// used for tests
@Synchronized
internal fun scheduledExecutorShutdownNow() {
    _scheduledExecutor?.shutdownNow()
}

@Synchronized
internal fun scheduledExecutorShutdownNowAndRelease() {
    _scheduledExecutor?.apply {
        shutdownNow()
        _scheduledExecutor = null
    }
}

/**
 * Runs a given suspending block of code inside a coroutine with a specified timeout and throws
 * [CancellationException] if timeout was exceeded.
 *
 * This function delegates to [Delay.invokeOnTimeout] if the context [CoroutineDispatcher]
 * implements [Delay] interface, otherwise it tracks time using a built-in single-threaded scheduled executor service.
 */
public suspend fun <T> withTimeout(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS, block: suspend () -> T): T {
    require(time >= 0) { "Timeout time $time cannot be negative" }
    if (time <= 0L) throw CancellationException("Timed out immediately")
    return suspendCancellableCoroutine sc@ { cont: CancellableContinuation<T> ->
        // schedule cancellation of this continuation on time
        val runnable = CancelTimedOutContinuationRunnable(time, unit, cont)
        val delay = cont.context[ContinuationInterceptor] as? Delay
        if (delay != null)
            cont.disposeOnCompletion(delay.invokeOnTimeout(time, unit, runnable)) else
            cont.cancelFutureOnCompletion(scheduledExecutor.schedule(runnable, time, unit))
        // restart block in a separate coroutine using cancellable context of this continuation,
        block.startCoroutine(cont)
    }
}

private class CancelTimedOutContinuationRunnable(
    private val time: Long,
    private val unit: TimeUnit,
    private val cont: CancellableContinuation<*>
): Runnable {
    override fun run() {
        cont.cancel(CancellationException("Timed out waiting for $time $unit"))
    }
    override fun toString(): String = "CancelTimedOutContinuationRunnable[$time,$unit,$cont]"
}
