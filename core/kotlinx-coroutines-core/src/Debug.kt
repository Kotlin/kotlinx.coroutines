/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.Continuation
import kotlinx.coroutines.internal.*

/**
 * Name of the property that controls coroutine debugging. See [newCoroutineContext][CoroutineScope.newCoroutineContext].
 */
public const val DEBUG_PROPERTY_NAME = "kotlinx.coroutines.debug"

/**
 * Name of the boolean property that controls stacktrace recovery (enabled by default) on JVM.
 * Stacktrace recovery is enabled if both debug and stacktrace recovery modes are enabled.
 *
 * Stacktrace recovery mode wraps every exception into the exception of the same type with original exception
 * as cause, but with stacktrace of the current coroutine.
 * Exception is instantiated using reflection by using no-arg, cause or cause and message constructor.
 * Stacktrace is not recovered if exception is an instance of [CancellationException] or [NonRecoverableThrowable].
 *
 * This mechanism is currently supported for channels, [async], [launch], [coroutineScope], [supervisorScope]
 * and [withContext] builders.
 */
internal const val STACKTRACE_RECOVERY_PROPERTY_NAME = "kotlinx.coroutines.stacktrace.recovery"

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

@JvmField
internal val DEBUG = systemProp(DEBUG_PROPERTY_NAME).let { value ->
    when (value) {
        DEBUG_PROPERTY_VALUE_AUTO, null -> CoroutineId::class.java.desiredAssertionStatus()
        DEBUG_PROPERTY_VALUE_ON, "" -> true
        DEBUG_PROPERTY_VALUE_OFF -> false
        else -> error("System property '$DEBUG_PROPERTY_NAME' has unrecognized value '$value'")
    }
}

@JvmField
internal val RECOVER_STACKTRACES = systemProp(STACKTRACE_RECOVERY_PROPERTY_NAME, true)

// internal debugging tools

internal actual val Any.hexAddress: String
    get() = Integer.toHexString(System.identityHashCode(this))

internal actual fun Continuation<*>.toDebugString(): String = when (this) {
    is DispatchedContinuation -> toString()
    else -> "$this@$hexAddress"
}

internal actual val Any.classSimpleName: String get() = this::class.java.simpleName
