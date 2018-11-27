/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlin.coroutines.*

internal actual fun <E: Throwable> recoverStackTrace(exception: E, continuation: Continuation<*>): E = exception
internal actual fun <E: Throwable> recoverStackTrace(exception: E): E = exception
internal actual fun <E : Throwable> unwrap(exception: E): E = exception
internal actual suspend inline fun recoverAndThrow(exception: Throwable): Nothing = throw exception

@Suppress("unused")
internal actual interface CoroutineStackFrame {
    public actual val callerFrame: CoroutineStackFrame?
    public actual fun getStackTraceElement(): StackTraceElement?
}

actual typealias StackTraceElement = Any
