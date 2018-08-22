/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

import kotlin.coroutines.experimental.*

/**
 * Tries to recover stacktrace for given [exception] and [continuation].
 * Stacktrace recovery tries to restore [continuation] stack frames using its debug metadata
 * and then reflectively instantiate exception of given type with original exception as a cause and
 * sets new stacktrace for wrapping exception.
 * Some frames may be missing due to tail-call elimination.
 * Implementation note: works only on JVM with enabled debug-mode
 */
internal expect fun <E: Throwable> recoverStackTrace(exception: E, continuation: Continuation<*>): E


/**
 * Tries to recover stacktrace for given [exception]. Used in non-suspendable points of awaiting.
 * Stacktrace recovery tries to instantiate exception of given type with original exception as a cause.
 * Wrapping exception will have proper stacktrace as it's instantiated in the right context.
 *
 * Implementation note: works only on JVM with enabled debug-mode
 */
internal expect fun <E: Throwable> recoverStackTrace(exception: E): E
