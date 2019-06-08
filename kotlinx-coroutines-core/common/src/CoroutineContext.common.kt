/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * Creates context for the new coroutine. It installs [Dispatchers.Default] when no other dispatcher nor
 * [ContinuationInterceptor] is specified, and adds optional support for debugging facilities (when turned on).
 */
public expect fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext

internal expect fun createDefaultDispatcher(): CoroutineDispatcher

@Suppress("PropertyName")
internal expect val DefaultDelay: Delay

// countOrElement -- pre-cached value for ThreadContext.kt
internal expect inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T
internal expect fun Continuation<*>.toDebugString(): String
internal expect val CoroutineContext.coroutineName: String?