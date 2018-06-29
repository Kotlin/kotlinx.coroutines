/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.Continuation

// internal debugging tools

internal actual val Any.hexAddress: String
    get() = Integer.toHexString(System.identityHashCode(this))

internal fun Any?.toSafeString(): String =
    try { toString() }
    catch (e: Throwable) { "toString() failed with $e" }

// **KLUDGE**: there is no reason to include continuation into debug string until the following ticket is resolved:
// KT-18986 Debug-friendly toString implementation for CoroutineImpl
// (the current string representation of continuation is useless and uses buggy reflection internals)
// So, this function is a replacement that extract a usable information from continuation -> its class name, at least
internal actual fun Continuation<*>.toDebugString(): String = when (this) {
    is DispatchedContinuation -> toString()
    else -> "${this::class.java.name}@$hexAddress"
}

internal actual val Any.classSimpleName: String get() = this::class.java.simpleName
