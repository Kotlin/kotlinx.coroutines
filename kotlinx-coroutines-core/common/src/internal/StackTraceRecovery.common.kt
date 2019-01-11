/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

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
internal expect fun <E: Throwable> unwrap(exception: E): E

internal expect class StackTraceElement

internal expect interface CoroutineStackFrame {
    public val callerFrame: CoroutineStackFrame?
    public fun getStackTraceElement(): StackTraceElement?
}

/**
 * Marker that indicates that stacktrace of the exception should not be recovered.
 * Currently internal, but may become public in the future
 */
internal interface NonRecoverableThrowable
