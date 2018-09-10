/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*

public expect fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext

@Suppress("PropertyName")
public expect val DefaultDispatcher: CoroutineDispatcher

@Suppress("PropertyName")
internal expect val DefaultDelay: Delay

internal expect inline fun <T> withCoroutineContext(context: CoroutineContext, block: () -> T): T
internal expect fun Continuation<*>.toDebugString(): String
internal expect val CoroutineContext.coroutineName: String?