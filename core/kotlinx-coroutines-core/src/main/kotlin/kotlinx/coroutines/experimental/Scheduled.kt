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

import kotlinx.coroutines.experimental.intrinsics.*
import kotlinx.coroutines.experimental.selects.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.*

/**
 * Runs a given suspending [block] of code inside a coroutine with a specified timeout and throws
 * [TimeoutCancellationException] if timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * cancellable suspending function inside the block throws [TimeoutCancellationException].
 * Even if the code in the block suppresses [TimeoutCancellationException], it
 * is still thrown by `withTimeout` invocation.
 *
 * The sibling function that does not throw exception on timeout is [withTimeoutOrNull].
 * Note, that timeout action can be specified for [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * This function delegates to [Delay.invokeOnTimeout] if the context [CoroutineDispatcher]
 * implements [Delay] interface, otherwise it tracks time using a built-in single-threaded scheduled executor service.
 *
 * @param time timeout time in milliseconds.
 */
public actual suspend fun <T> withTimeout(time: Int, block: suspend CoroutineScope.() -> T): T =
    withTimeout(time.toLong(), TimeUnit.MILLISECONDS, block)

/**
 * Runs a given suspending [block] of code inside a coroutine with a specified timeout and throws
 * [TimeoutCancellationException] if timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * cancellable suspending function inside the block throws [TimeoutCancellationException].
 * Even if the code in the block suppresses [TimeoutCancellationException], it
 * is still thrown by `withTimeout` invocation.
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
public suspend fun <T> withTimeout(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS, block: suspend CoroutineScope.() -> T): T {
    require(time >= 0) { "Timeout time $time cannot be negative" }
    if (time <= 0L) throw CancellationException("Timed out immediately")
    return suspendCoroutineOrReturn { cont: Continuation<T> ->
        setupTimeout(TimeoutCoroutine(time, unit, cont), block)
    }
}

private fun <U, T: U> setupTimeout(
    coroutine: TimeoutCoroutine<U, T>,
    block: suspend CoroutineScope.() -> T
): Any? {
    // schedule cancellation of this coroutine on time
    val cont = coroutine.cont
    val context = cont.context
    coroutine.disposeOnCompletion(context.delay.invokeOnTimeout(coroutine.time, coroutine.unit, coroutine))
    // restart block using new coroutine with new job,
    // however start it as undispatched coroutine, because we are already in the proper context
    return coroutine.startUndispatchedOrReturn(coroutine, block)
}

/**
 * @suppress **Deprecated**: for binary compatibility only
 */
@Deprecated("for binary compatibility only", level=DeprecationLevel.HIDDEN)
public suspend fun <T> withTimeout(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS, block: suspend () -> T): T =
    withTimeout(time, unit) { block() }

private open class TimeoutCoroutine<U, in T: U>(
    @JvmField val time: Long,
    @JvmField val unit: TimeUnit,
    @JvmField val cont: Continuation<U>
) : AbstractCoroutine<T>(cont.context, active = true), Runnable, Continuation<T> {
    override val defaultResumeMode: Int get() = MODE_DIRECT

    @Suppress("LeakingThis")
    override fun run() {
        cancel(TimeoutCancellationException(time, unit, this))
    }

    @Suppress("UNCHECKED_CAST")
    internal override fun onCompletionInternal(state: Any?, mode: Int) {
        if (state is CompletedExceptionally)
            cont.resumeWithExceptionMode(state.exception, mode)
        else
            cont.resumeMode(state as T, mode)
    }

    override fun nameString(): String =
        "${super.nameString()}($time $unit)"
}

/**
 * Runs a given suspending block of code inside a coroutine with a specified timeout and returns
 * `null` if this timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * cancellable suspending function inside the block throws [TimeoutCancellationException].
 * Even if the code in the block suppresses [TimeoutCancellationException], this
 * invocation of `withTimeoutOrNull` still returns `null`.
 *
 * The sibling function that throws exception on timeout is [withTimeout].
 * Note, that timeout action can be specified for [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * This function delegates to [Delay.invokeOnTimeout] if the context [CoroutineDispatcher]
 * implements [Delay] interface, otherwise it tracks time using a built-in single-threaded scheduled executor service.
 *
 * @param time timeout time in milliseconds.
 */
public actual suspend fun <T> withTimeoutOrNull(time: Int, block: suspend CoroutineScope.() -> T): T? =
    withTimeoutOrNull(time.toLong(), TimeUnit.MILLISECONDS, block)

/**
 * Runs a given suspending block of code inside a coroutine with a specified timeout and returns
 * `null` if this timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * cancellable suspending function inside the block throws [TimeoutCancellationException].
 * Even if the code in the block suppresses [TimeoutCancellationException], this
 * invocation of `withTimeoutOrNull` still returns `null`.
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
public suspend fun <T> withTimeoutOrNull(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS, block: suspend CoroutineScope.() -> T): T? {
    require(time >= 0) { "Timeout time $time cannot be negative" }
    if (time <= 0L) return null
    return suspendCoroutineOrReturn { cont: Continuation<T?> ->
        setupTimeout(TimeoutOrNullCoroutine(time, unit, cont), block)
    }
}

/**
 * @suppress **Deprecated**: for binary compatibility only
 */
@Deprecated("for binary compatibility only", level=DeprecationLevel.HIDDEN)
public suspend fun <T> withTimeoutOrNull(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS, block: suspend () -> T): T? =
    withTimeoutOrNull(time, unit) { block() }

private class TimeoutOrNullCoroutine<T>(
    time: Long,
    unit: TimeUnit,
    cont: Continuation<T?>
) : TimeoutCoroutine<T?, T>(time, unit, cont) {
    @Suppress("UNCHECKED_CAST")
    internal override fun onCompletionInternal(state: Any?, mode: Int) {
        if (state is CompletedExceptionally) {
            val exception = state.exception
            if (exception is TimeoutCancellationException && exception.coroutine === this)
                cont.resumeMode(null, mode) else
                cont.resumeWithExceptionMode(exception, mode)
        } else
            cont.resumeMode(state as T, mode)
    }
}

