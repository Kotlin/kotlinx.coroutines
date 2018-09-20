/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.*
import kotlin.coroutines.experimental.Continuation

/**
 * Name of the property that controls coroutine debugging. See [newCoroutineContext][CoroutineScope.newCoroutineContext].
 */
public const val DEBUG_PROPERTY_NAME = "kotlinx.coroutines.debug"

/**
 * Automatic debug configuration value for [DEBUG_PROPERTY_NAME]. See [newCoroutineContext][CoroutineScope.newCoroutineContext].
 */
public const val DEBUG_PROPERTY_VALUE_AUTO = "auto"

/**
 * Debug turned on value for [DEBUG_PROPERTY_NAME]. See [newCoroutineContext][CoroutineScope.newCoroutineContext].
 */
public const val DEBUG_PROPERTY_VALUE_ON = "on"

/**
 * Debug turned on value for [DEBUG_PROPERTY_NAME]. See [newCoroutineContext][CoroutineScope.newCoroutineContext].
 */
public const val DEBUG_PROPERTY_VALUE_OFF = "off"

internal val DEBUG = systemProp(DEBUG_PROPERTY_NAME).let { value ->
    when (value) {
        DEBUG_PROPERTY_VALUE_AUTO, null -> CoroutineId::class.java.desiredAssertionStatus()
        DEBUG_PROPERTY_VALUE_ON, "" -> true
        DEBUG_PROPERTY_VALUE_OFF -> false
        else -> error("System property '$DEBUG_PROPERTY_NAME' has unrecognized value '$value'")
    }
}

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
