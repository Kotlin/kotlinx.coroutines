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

import kotlinx.coroutines.experimental.intrinsics.startCoroutineUndispatched
import kotlinx.coroutines.experimental.selects.SelectBuilder
import kotlinx.coroutines.experimental.selects.select
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.ScheduledThreadPoolExecutor
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

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
 * Runs a given suspending [block] of code inside a coroutine with a specified timeout and throws
 * [CancellationException] if timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and throws [CancellationException]
 * exception inside of it, too. However, even the code in the block suppresses the exception,
 * this `withTimeout` function invocation still throws [CancellationException].
 *
 * The sibling function that does not throw exception on timeout is [withTimeoutOrNull].
 * Note, that timeout action can be specified for [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * This function delegates to [Delay.invokeOnTimeout] if the context [CoroutineDispatcher]
 * implements [Delay] interface, otherwise it tracks time using a built-in single-threaded scheduled executor service.
 *
 * @param time timeout time
 * @param unit timeout unit (milliseconds by default)
 */
public suspend fun <T> withTimeout(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS, block: suspend () -> T): T {
    require(time >= 0) { "Timeout time $time cannot be negative" }
    if (time <= 0L) throw CancellationException("Timed out immediately")
    return suspendCoroutineOrReturn sc@ { delegate: Continuation<T> ->
        // schedule cancellation of this continuation on time
        val cont = TimeoutExceptionContinuation(time, unit, delegate)
        val delay = cont.context[ContinuationInterceptor] as? Delay
        if (delay != null)
            cont.disposeOnCompletion(delay.invokeOnTimeout(time, unit, cont)) else
            cont.cancelFutureOnCompletion(scheduledExecutor.schedule(cont, time, unit))
        // restart block using cancellable context of this continuation,
        // however start it as undispatched coroutine, because we are already in the proper context
        block.startCoroutineUndispatched(cont)
        cont.getResult()
    }
}

/**
 * Runs a given suspending block of code inside a coroutine with a specified timeout and returns
 * `null` if timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and throws [CancellationException]
 * exception inside of it. However, even the code in the block does not catch the cancellation exception,
 * this `withTimeoutOrNull` function invocation still returns `null` on timeout.
 *
 * The sibling function that throws exception on timeout is [withTimeout].
 * Note, that timeout action can be specified for [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * This function delegates to [Delay.invokeOnTimeout] if the context [CoroutineDispatcher]
 * implements [Delay] interface, otherwise it tracks time using a built-in single-threaded scheduled executor service.
 *
 * @param time timeout time
 * @param unit timeout unit (milliseconds by default)
 */
public suspend fun <T> withTimeoutOrNull(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS, block: suspend () -> T): T? {
    require(time >= 0) { "Timeout time $time cannot be negative" }
    if (time <= 0L) return null
    return suspendCoroutineOrReturn sc@ { delegate: Continuation<T?> ->
        // schedule cancellation of this continuation on time
        val cont = TimeoutNullContinuation<T>(delegate)
        val delay = cont.context[ContinuationInterceptor] as? Delay
        if (delay != null)
            cont.disposeOnCompletion(delay.invokeOnTimeout(time, unit, cont)) else
            cont.cancelFutureOnCompletion(scheduledExecutor.schedule(cont, time, unit))
        // restart block using cancellable context of this continuation,
        // however start it as undispatched coroutine, because we are already in the proper context
        block.startCoroutineUndispatched(cont)
        cont.getResult()
    }
}

private class TimeoutExceptionContinuation<in T>(
    private val time: Long,
    private val unit: TimeUnit,
    delegate: Continuation<T>
) : CancellableContinuationImpl<T>(delegate, active = true), Runnable {
    override val defaultResumeMode get() = MODE_DIRECT
    override fun run() { cancel(CancellationException("Timed out waiting for $time $unit")) }
}

private class TimeoutNullContinuation<in T>(
    delegate: Continuation<T?>
) : CancellableContinuationImpl<T?>(delegate, active = true), Runnable {
    override val defaultResumeMode get() = MODE_DIRECT
    override val ignoreRepeatedResume: Boolean get() = true
    override fun run() { resume(null, mode = 0) /* dispatch resume */ }
}
