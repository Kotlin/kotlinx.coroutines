@file:OptIn(ExperimentalContracts::class)
@file:Suppress("LEAKED_IN_PLACE_LAMBDA", "WRONG_INVOCATION_KIND")

package kotlinx.coroutines.timeout

import kotlinx.coroutines.*
import kotlin.contracts.*
import kotlin.coroutines.Continuation
import kotlin.coroutines.intrinsics.suspendCoroutineUninterceptedOrReturn
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds

/**
 * [kotlinx.coroutines.withTimeout] but better
 */
public suspend fun <T> withTimeout(timeMillis: Long, block: suspend CoroutineScope.() -> T): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    if (timeMillis <= 0L) throw TimeoutException("Timed out immediately")
    return suspendCoroutineUninterceptedOrReturn { uCont ->
        setupTimeout(TimeoutCoroutine(timeMillis, uCont), block)
    }
}

internal class TimeoutCoroutine<U, in T : U>(
    time: Long,
    uCont: Continuation<U> // unintercepted continuation
) : TimeoutCoroutineBase<U, T>(time, uCont) {
    override fun timeoutException(): Throwable = TimeoutException(time, context.delay, this)
}

/**
 * [kotlinx.coroutines.withTimeout] but better
 */
public suspend fun <T> withTimeout(timeout: Duration, block: suspend CoroutineScope.() -> T): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return withTimeout(timeout.toDelayMillis(), block)
}

/**
 * This exception is thrown by [withTimeout] to indicate timeout.
 *
 * Example of usage:
 * ```
 * suspend fun main() {
 *     try {
 *         val result = withTimeout(100.milliseconds) {
 *             println("Executing long-running operation")
 *             delay(1.seconds) // Pretending to be slow operation
 *             42
 *         }
 *         println("Computation result: $result") // Never printed
 *     } catch (e: TimeoutException) {
 *         println("Computation failed: ${e.message}")
 *     }
 * }
 * ```
 *
 * ### Implementation note
 *
 * On the JVM platform, this exception extends `java.util.concurrent.TimeoutException`.
 * The main purpose of that is to make `java.util.concurrent.TimeoutException` and `kotlinx.coroutines.TimeoutException`
 * interchangeable from the user perspective (i.e. any of them can be caught) and thus less error-prone,
 * while allowing the implementation to store auxilary data along with the exception.
 */
public expect class TimeoutException internal constructor(message: String, coroutine: Job?) : Exception {
    internal constructor(message: String)
}

private fun TimeoutException(
    time: Long,
    delay: Delay,
    coroutine: Job
): TimeoutException {
    val message = (delay as? DelayWithTimeoutDiagnostics)?.timeoutMessage(time.milliseconds)
        ?: "Timed out waiting for $time ms"
    return TimeoutException(message, coroutine)
}
