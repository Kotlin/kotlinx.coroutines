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

import kotlinx.coroutines.experimental.selects.SelectBuilder
import kotlinx.coroutines.experimental.selects.select
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.intrinsics.startCoroutineUninterceptedOrReturn
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

/**
 * Runs a given suspending [block] of code inside a coroutine with a specified timeout and throws
 * [TimeoutCancellationException] if timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * cancellable suspending function inside the block throws [TimeoutCancellationException], so normally that exception,
 * if uncaught, also gets thrown by `withTimeout` as a result.
 * However, the code in the block can suppress [TimeoutCancellationException].
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
    return suspendCoroutineOrReturn { cont: Continuation<T> ->
        val context = cont.context
        val completion = TimeoutCompletion(time, unit, cont)
        // schedule cancellation of this coroutine on time
        completion.disposeOnCompletion(context.delay.invokeOnTimeout(time, unit, completion))
        completion.initParentJob(context[Job])
        // restart block using new coroutine with new job,
        // however start it as undispatched coroutine, because we are already in the proper context
        block.startCoroutineUninterceptedOrReturn(completion)
    }
}

private open class TimeoutCompletion<U, in T: U>(
    private val time: Long,
    private val unit: TimeUnit,
    @JvmField protected val cont: Continuation<U>
) : JobSupport(active = true), Runnable, Continuation<T> {
    @Suppress("LeakingThis")
    override val context: CoroutineContext = cont.context + this // mix in this Job into the context
    override fun run() { cancel(TimeoutCancellationException(time, unit, this)) }
    override fun resume(value: T) { cont.resumeDirect(value) }
    override fun resumeWithException(exception: Throwable) { cont.resumeDirectWithException(exception) }
}

/**
 * Runs a given suspending block of code inside a coroutine with a specified timeout and returns
 * `null` if this timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * cancellable suspending function inside the block throws [TimeoutCancellationException]. Normally that exception,
 * if uncaught by the block, gets converted into the `null` result of `withTimeoutOrNull`.
 * However, the code in the block can suppress [TimeoutCancellationException].
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
    return suspendCoroutineOrReturn { cont: Continuation<T?> ->
        val context = cont.context
        val completion = TimeoutOrNullCompletion(time, unit, cont)
        // schedule cancellation of this coroutine on time
        completion.disposeOnCompletion(context.delay.invokeOnTimeout(time, unit, completion))
        completion.initParentJob(context[Job])
        // restart block using new coroutine with new job,
        // however start it as undispatched coroutine, because we are already in the proper context
        try {
            block.startCoroutineUninterceptedOrReturn(completion)
        } catch (e: TimeoutCancellationException) {
            // replace inner timeout exception on our coroutine with null result
            if (e.coroutine == completion) null else throw e
        }
    }
}

private class TimeoutOrNullCompletion<T>(
    time: Long,
    unit: TimeUnit,
    cont: Continuation<T?>
) : TimeoutCompletion<T?, T>(time, unit, cont) {
    override fun resumeWithException(exception: Throwable) {
        // suppress inner timeout exception and replace it with null
        if (exception is TimeoutCancellationException && exception.coroutine === this)
            cont.resumeDirect(null) else
            cont.resumeDirectWithException(exception)
    }
}

/**
 * This exception is thrown by [withTimeout] to indicate timeout.
 */
@Suppress("DEPRECATION")
public class TimeoutCancellationException internal constructor(
    message: String,
    @JvmField internal val coroutine: Job?
) : TimeoutException(message) {
    /**
     * Creates timeout exception with a given message.
     */
    public constructor(message: String) : this(message, null)
}

/**
 * @suppress **Deprecated**: Renamed to TimeoutCancellationException
 */
@Deprecated("Renamed to TimeoutCancellationException", replaceWith = ReplaceWith("TimeoutCancellationException"))
public open class TimeoutException(message: String) : CancellationException(message)

private fun TimeoutCancellationException(
    time: Long,
    unit: TimeUnit,
    coroutine: Job
) : TimeoutCancellationException = TimeoutCancellationException("Timed out waiting for $time $unit", coroutine)
