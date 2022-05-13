/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*
import kotlin.time.*

/**
 * Runs a given suspending [block] of code inside a coroutine with a specified [timeout][timeMillis] and throws
 * a [TimeoutCancellationException] if the timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * the cancellable suspending function inside the block throws a [TimeoutCancellationException].
 *
 * The sibling function that does not throw an exception on timeout is [withTimeoutOrNull].
 * Note that the timeout action can be specified for a [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * **The timeout event is asynchronous with respect to the code running in the block** and may happen at any time,
 * even right before the return from inside of the timeout [block]. Keep this in mind if you open or acquire some
 * resource inside the [block] that needs closing or release outside of the block.
 * See the
 * [Asynchronous timeout and resources][https://kotlinlang.org/docs/reference/coroutines/cancellation-and-timeouts.html#asynchronous-timeout-and-resources]
 * section of the coroutines guide for details.
 *
 * > Implementation note: how the time is tracked exactly is an implementation detail of the context's [CoroutineDispatcher].
 *
 * @param timeMillis timeout time in milliseconds.
 */
public suspend fun <T> withTimeout(timeMillis: Long, block: suspend CoroutineScope.() -> T): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    if (timeMillis <= 0L) throw TimeoutCancellationException("Timed out immediately")
    return suspendCoroutineUninterceptedOrReturn { uCont ->
        setupTimeout(TimeoutCoroutine(timeMillis, uCont), block)
    }
}

/**
 * Runs a given suspending [block] of code inside a coroutine with the specified [timeout] and throws
 * a [TimeoutCancellationException] if the timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * the cancellable suspending function inside the block throws a [TimeoutCancellationException].
 *
 * The sibling function that does not throw an exception on timeout is [withTimeoutOrNull].
 * Note that the timeout action can be specified for a [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * **The timeout event is asynchronous with respect to the code running in the block** and may happen at any time,
 * even right before the return from inside of the timeout [block]. Keep this in mind if you open or acquire some
 * resource inside the [block] that needs closing or release outside of the block.
 * See the
 * [Asynchronous timeout and resources][https://kotlinlang.org/docs/reference/coroutines/cancellation-and-timeouts.html#asynchronous-timeout-and-resources]
 * section of the coroutines guide for details.
 *
 * > Implementation note: how the time is tracked exactly is an implementation detail of the context's [CoroutineDispatcher].
 */
public suspend fun <T> withTimeout(timeout: Duration, block: suspend CoroutineScope.() -> T): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return withTimeout(timeout.toDelayMillis(), block)
}

/**
 * Runs a given suspending block of code inside a coroutine with a specified [timeout][timeMillis] and returns
 * `null` if this timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * cancellable suspending function inside the block throws a [TimeoutCancellationException].
 *
 * The sibling function that throws an exception on timeout is [withTimeout].
 * Note that the timeout action can be specified for a [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * **The timeout event is asynchronous with respect to the code running in the block** and may happen at any time,
 * even right before the return from inside of the timeout [block]. Keep this in mind if you open or acquire some
 * resource inside the [block] that needs closing or release outside of the block.
 * See the
 * [Asynchronous timeout and resources][https://kotlinlang.org/docs/reference/coroutines/cancellation-and-timeouts.html#asynchronous-timeout-and-resources]
 * section of the coroutines guide for details.
 *
 * > Implementation note: how the time is tracked exactly is an implementation detail of the context's [CoroutineDispatcher].
 *
 * @param timeMillis timeout time in milliseconds.
 */
public suspend fun <T> withTimeoutOrNull(timeMillis: Long, block: suspend CoroutineScope.() -> T): T? {
    if (timeMillis <= 0L) return null

    var coroutine: TimeoutCoroutine<T?, T?>? = null
    try {
        return suspendCoroutineUninterceptedOrReturn { uCont ->
            val timeoutCoroutine = TimeoutCoroutine(timeMillis, uCont)
            coroutine = timeoutCoroutine
            setupTimeout<T?, T?>(timeoutCoroutine, block)
        }
    } catch (e: TimeoutCancellationException) {
        // Return null if it's our exception, otherwise propagate it upstream (e.g. in case of nested withTimeouts)
        if (e.coroutine === coroutine) {
            return null
        }
        throw e
    }
}

/**
 * Runs a given suspending block of code inside a coroutine with the specified [timeout] and returns
 * `null` if this timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * cancellable suspending function inside the block throws a [TimeoutCancellationException].
 *
 * The sibling function that throws an exception on timeout is [withTimeout].
 * Note that the timeout action can be specified for a [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * **The timeout event is asynchronous with respect to the code running in the block** and may happen at any time,
 * even right before the return from inside of the timeout [block]. Keep this in mind if you open or acquire some
 * resource inside the [block] that needs closing or release outside of the block.
 * See the
 * [Asynchronous timeout and resources][https://kotlinlang.org/docs/reference/coroutines/cancellation-and-timeouts.html#asynchronous-timeout-and-resources]
 * section of the coroutines guide for details.
 *
 * > Implementation note: how the time is tracked exactly is an implementation detail of the context's [CoroutineDispatcher].
 */
public suspend fun <T> withTimeoutOrNull(timeout: Duration, block: suspend CoroutineScope.() -> T): T? =
        withTimeoutOrNull(timeout.toDelayMillis(), block)

private fun <U, T: U> setupTimeout(
    coroutine: TimeoutCoroutine<U, T>,
    block: suspend CoroutineScope.() -> T
): Any? {
    // schedule cancellation of this coroutine on time
    val cont = coroutine.uCont
    val context = cont.context
    coroutine.disposeOnCompletion(context.delay.invokeOnTimeout(coroutine.time, coroutine, coroutine.context))
    // restart the block using a new coroutine with a new job,
    // however, start it undispatched, because we already are in the proper context
    return coroutine.startUndispatchedOrReturnIgnoreTimeout(coroutine, block)
}

private class TimeoutCoroutine<U, in T: U>(
    @JvmField val time: Long,
    uCont: Continuation<U> // unintercepted continuation
) : ScopeCoroutine<T>(uCont.context, uCont), Runnable {
    override fun run() {
        cancelCoroutine(TimeoutCancellationException(time, this))
    }

    override fun nameString(): String =
        "${super.nameString()}(timeMillis=$time)"
}

/**
 * This exception is thrown by [withTimeout] to indicate timeout.
 */
public class TimeoutCancellationException internal constructor(
    message: String,
    @JvmField internal val coroutine: Job?
) : CancellationException(message), CopyableThrowable<TimeoutCancellationException> {
    /**
     * Creates a timeout exception with the given message.
     * This constructor is needed for exception stack-traces recovery.
     */
    @Suppress("UNUSED")
    internal constructor(message: String) : this(message, null)

    // message is never null in fact
    override fun createCopy(): TimeoutCancellationException? =
        TimeoutCancellationException(message ?: "", coroutine).also { it.initCause(this) }
}

@Suppress("FunctionName")
internal fun TimeoutCancellationException(
    time: Long,
    coroutine: Job
) : TimeoutCancellationException = TimeoutCancellationException("Timed out waiting for $time ms", coroutine)
