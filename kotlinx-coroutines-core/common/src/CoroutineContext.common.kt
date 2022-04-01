/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * Creates a context for a new coroutine. It installs [Dispatchers.Default] when no other dispatcher or
 * [ContinuationInterceptor] is specified and adds optional support for debugging facilities (when turned on)
 * and copyable-thread-local facilities on JVM.
 */
public expect fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext

/**
 * Creates a context for coroutine builder functions that do not launch a new coroutine, e.g. [withContext].
 * @suppress
 */
@InternalCoroutinesApi
public expect fun CoroutineContext.newCoroutineContext(addedContext: CoroutineContext): CoroutineContext

@PublishedApi
@Suppress("PropertyName")
internal expect val DefaultDelay: Delay

// countOrElement -- pre-cached value for ThreadContext.kt
internal expect inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T
internal expect inline fun <T> withContinuationContext(continuation: Continuation<*>, countOrElement: Any?, block: () -> T): T
internal expect fun Continuation<*>.toDebugString(): String
internal expect val CoroutineContext.coroutineName: String?
