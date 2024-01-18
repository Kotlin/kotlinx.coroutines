package kotlinx.coroutines.internal

import kotlin.coroutines.*

/**
 * Tries to recover stacktrace for given [exception] and [continuation].
 * Stacktrace recovery tries to restore [continuation] stack frames using its debug metadata with [CoroutineStackFrame] API
 * and then reflectively instantiate exception of given type with original exception as a cause and
 * sets new stacktrace for wrapping exception.
 * Some frames may be missing due to tail-call elimination.
 *
 * Works only on JVM with enabled debug-mode.
 */
internal expect fun <E: Throwable> recoverStackTrace(exception: E, continuation: Continuation<*>): E

/**
 * initCause on JVM, nop on other platforms
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
internal expect fun Throwable.initCause(cause: Throwable)

/**
 * Tries to recover stacktrace for given [exception]. Used in non-suspendable points of awaiting.
 * Stacktrace recovery tries to instantiate exception of given type with original exception as a cause.
 * Wrapping exception will have proper stacktrace as it's instantiated in the right context.
 *
 * Works only on JVM with enabled debug-mode.
 */
internal expect fun <E: Throwable> recoverStackTrace(exception: E): E

// Name conflict with recoverStackTrace
@Suppress("NOTHING_TO_INLINE")
internal expect suspend inline fun recoverAndThrow(exception: Throwable): Nothing

/**
 * The opposite of [recoverStackTrace].
 * It is guaranteed that `unwrap(recoverStackTrace(e)) === e`
 */
@PublishedApi // Used from kotlinx-coroutines-test and reactor modules via suppress, not part of ABI
internal expect fun <E: Throwable> unwrap(exception: E): E

internal expect class StackTraceElement

internal expect interface CoroutineStackFrame {
    public val callerFrame: CoroutineStackFrame?
    public fun getStackTraceElement(): StackTraceElement?
}
