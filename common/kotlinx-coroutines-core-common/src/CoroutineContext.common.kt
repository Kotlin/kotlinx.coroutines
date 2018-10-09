/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

public expect fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext

internal expect fun createDefaultDispatcher(): CoroutineDispatcher

@Suppress("PropertyName")
internal expect val DefaultDelay: Delay

internal expect inline fun <T> withCoroutineContext(context: CoroutineContext, block: () -> T): T
internal expect fun Continuation<*>.toDebugString(): String
internal expect val CoroutineContext.coroutineName: String?