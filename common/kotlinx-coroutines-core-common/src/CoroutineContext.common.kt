/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:UseExperimental(ExperimentalTypeInference::class)

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.experimental.*

@BuilderInference
public expect fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext

/**
 * The default [CoroutineDispatcher] that is used by all standard builders.
 * @suppress **Deprecated**: Use [Dispatchers.Default].
 */
@Suppress("PropertyName")
@Deprecated(
    message = "Use Dispatchers.Default",
    replaceWith = ReplaceWith("Dispatchers.Default",
        imports = ["kotlinx.coroutines.Dispatchers"]))
public expect val DefaultDispatcher: CoroutineDispatcher

internal expect fun createDefaultDispatcher(): CoroutineDispatcher

@Suppress("PropertyName")
internal expect val DefaultDelay: Delay

internal expect inline fun <T> withCoroutineContext(context: CoroutineContext, block: () -> T): T
internal expect fun Continuation<*>.toDebugString(): String
internal expect val CoroutineContext.coroutineName: String?