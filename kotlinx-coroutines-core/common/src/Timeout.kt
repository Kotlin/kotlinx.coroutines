@file:OptIn(ExperimentalContracts::class)
@file:Suppress("LEAKED_IN_PLACE_LAMBDA", "WRONG_INVOCATION_KIND")

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*
import kotlin.time.*
import kotlin.time.Duration.Companion.milliseconds

/**
 * Shortcut for calling [withTimeout] with a [Duration] timeout of [timeMillis] milliseconds.
 * Please see that overload for details.
 *
 * > Note: the behavior of this function can be different from [withTimeout] if [timeMillis] is greater than
 * `Long.MAX_VALUE / 2` milliseconds.
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
 * Calls the specified suspending [block] with the specified [timeout], suspends until it completes,
 * and returns the result.
 *
 * If the [block] execution times out, it is cancelled with a [TimeoutCancellationException].
 * If the [timeout] is non-positive, this happens immediately and the [block] is not executed.
 *
 * The cancellation on timeout is asynchronous with respect to the code running in the block
 * and may happen at any time, even after the [block] finishes executing but before the caller gets resumed with
 * the result.
 *
 * > Implementation note: how the time is tracked exactly is an implementation detail of the context's [CoroutineDispatcher].
 *
 * ## Structured Concurrency
 *
 * [withTimeout] behaves like [coroutineScope], as it, too, creates a new *scoped child coroutine*.
 * Refer to the documentation of [coroutineScope] for details.
 *
 * ## Pitfalls
 *
 * ### Cancellation is cooperative
 *
 * [withTimeout] will not automatically stop all code inside it from being executed once the timeout gets triggered.
 * It only cancels the running [block], but it's up to the [block] to notice that it was cancelled, for example,
 * using [ensureActive], checking [isActive], or using [suspendCancellableCoroutine].
 *
 * For example, this JVM code will run to completion, taking 10 seconds to do so:
 *
 * ```
 * withTimeout(1.seconds) {
 *     Thread.sleep(10_000)
 * }
 * ```
 *
 * On the JVM, use the `runInterruptible` function to propagate cancellations
 * to blocking JVM code as thread interruptions.
 *
 * See the [Cancellation is cooperative](https://kotlinlang.org/docs/cancellation-and-timeouts.html#cancellation-is-cooperative).
 * section of the coroutines guide for details.
 *
 * ### [TimeoutCancellationException] is not considered an error
 *
 * Consider this code:
 *
 * ```
 * coroutineScope {
 *     launch {
 *         withTimeout(10.milliseconds) {
 *             // Some operation that is going to time out
 *             awaitCancellation()
 *         }
 *     }
 * }
 * ```
 *
 * Here, the timeout will be triggered, and [withTimeout] will finish with a [TimeoutCancellationException].
 * However, [coroutineScope] will finish normally.
 * The reason is that when coroutines finish with a [CancellationException],
 * the error does not get propagated to the parent, just like it doesn't when a child actually gets cancelled.
 *
 * For ensuring that timeouts are treated as true errors that should cause the parent to fail,
 * use [withTimeoutOrNull] and check the return value:
 *
 * ```
 * coroutineScope {
 *     launch {
 *         withTimeoutOrNull(10.milliseconds) {
 *             // Some operation that is going to time out
 *             awaitCancellation()
 *         } ?: error("Timed out!")
 *     }
 * }
 * ```
 *
 * If [withTimeout] has to return a nullable value and [withTimeoutOrNull] can not be used,
 * this pattern can help instead:
 *
 * ```
 * coroutineScope {
 *     launch {
 *         try {
 *             withTimeoutOrNull(10.milliseconds) {
 *                 // Some operation that is going to time out
 *                 awaitCancellation()
 *             }
 *         } catch (e: TimeoutCancellationException) {
 *             error("Timed out!")
 *         }
 *     }
 * }
 * ```
 *
 * Another option is to specify the timeout action in a [select] invocation
 * with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * ### Returning closeable resources
 *
 * Values returned from [withTimeout] will typically be lost if the caller is cancelled.
 *
 * See the corresponding section in the [coroutineScope] documentation for details.
 *
 * @see withTimeoutOrNull
 * @see SelectBuilder.onTimeout
 */
public suspend fun <T> withTimeout(timeout: Duration, block: suspend CoroutineScope.() -> T): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return withTimeout(timeout.toDelayMillis(), block)
}

/**
 * Shortcut for calling [withTimeoutOrNull] with a [Duration] timeout of [timeMillis] milliseconds.
 * Please see that overload for details.
 *
 * > Note: the behavior of this function can be different from [withTimeoutOrNull] if [timeMillis] is greater than
 * `Long.MAX_VALUE / 2` milliseconds.
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
 * Calls the specified suspending [block] with the specified [timeout], suspends until it completes,
 * and returns the result.
 *
 * If the [block] execution times out, it is cancelled with a [TimeoutCancellationException].
 * If the [timeout] is non-positive, this happens immediately and the [block] is not executed.
 *
 * The cancellation on timeout is asynchronous with respect to the code running in the block
 * and may happen at any time, even after the [block] finishes executing but before the caller gets resumed with
 * the result.
 *
 * > Implementation note: how the time is tracked exactly is an implementation detail of the context's [CoroutineDispatcher].
 *
 * ## Structured Concurrency
 *
 * [withTimeoutOrNull] behaves like [coroutineScope], as it, too, creates a new *scoped child coroutine*.
 * Refer to the documentation of [coroutineScope] for details.
 *
 * ## Pitfalls
 *
 * ### Cancellation is cooperative
 *
 * [withTimeoutOrNull] will not automatically stop all code inside it from being executed
 * once the timeout gets triggered.
 * It only cancels the running [block], but it's up to the [block] to notice that it was cancelled, for example,
 * using [ensureActive], checking [isActive], or using [suspendCancellableCoroutine].
 *
 * For example, this JVM code will run to completion, taking 10 seconds to do so:
 *
 * ```
 * withTimeout(1.seconds) {
 *     Thread.sleep(10_000)
 * }
 * ```
 *
 * On the JVM, use the `runInterruptible` function to propagate cancellations
 * to blocking JVM code as thread interruptions.
 *
 * See the [Cancellation is cooperative](https://kotlinlang.org/docs/cancellation-and-timeouts.html#cancellation-is-cooperative).
 * section of the coroutines guide for details.
 *
 * ### Returning closeable resources
 *
 * Values returned from [withTimeoutOrNull] will typically be lost if the caller is cancelled.
 *
 * See the corresponding section in the [coroutineScope] documentation for details.
 *
 * @see withTimeoutOrNull
 * @see SelectBuilder.onTimeout
 */
public suspend fun <T> withTimeoutOrNull(timeout: Duration, block: suspend CoroutineScope.() -> T): T? =
    withTimeoutOrNull(timeout.toDelayMillis(), block)

private fun <U, T : U> setupTimeout(
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

private class TimeoutCoroutine<U, in T : U>(
    @JvmField val time: Long,
    uCont: Continuation<U> // unintercepted continuation
) : ScopeCoroutine<T>(uCont.context, uCont), Runnable {
    override fun run() {
        cancelCoroutine(TimeoutCancellationException(time, context.delay, this))
    }

    override fun nameString(): String =
        "${super.nameString()}(timeMillis=$time)"
}

/**
 * This exception is thrown by [withTimeout] to indicate timeout.
 */
public class TimeoutCancellationException internal constructor(
    message: String,
    @JvmField @Transient internal val coroutine: Job?
) : CancellationException(message), CopyableThrowable<TimeoutCancellationException> {
    /**
     * Creates a timeout exception with the given message.
     * This constructor is needed for exception stack-traces recovery.
     */
    internal constructor(message: String) : this(message, null)

    // message is never null in fact
    override fun createCopy(): TimeoutCancellationException =
        TimeoutCancellationException(message ?: "", coroutine).also { it.initCause(this) }
}

internal fun TimeoutCancellationException(
    time: Long,
    delay: Delay,
    coroutine: Job
) : TimeoutCancellationException {
    val message = (delay as? DelayWithTimeoutDiagnostics)?.timeoutMessage(time.milliseconds)
        ?: "Timed out waiting for $time ms"
    return TimeoutCancellationException(message, coroutine)
}
