/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.native.*

internal actual fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher =
    MissingMainDispatcher

internal actual fun createDefaultDispatcher(): CoroutineDispatcher = DefaultDispatcher

private object DefaultDispatcher : CoroutineDispatcher() {
    // Be consistent with JVM -- at least 2 threads to provide some liveness guarantees in case of improper uses
    @OptIn(ExperimentalStdlibApi::class)
    private val ctx = newFixedThreadPoolContext(Platform.getAvailableProcessors().coerceAtLeast(2), "Dispatchers.Default")

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        ctx.dispatch(context, block)
    }
}

private object MissingMainDispatcher : MainCoroutineDispatcher() {
    override val immediate: MainCoroutineDispatcher
        get() = notImplemented()
    override fun dispatch(context: CoroutineContext, block: Runnable) = notImplemented()
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = notImplemented()
    override fun dispatchYield(context: CoroutineContext, block: Runnable) = notImplemented()

    private fun notImplemented(): Nothing = TODO("Dispatchers.Main is missing on the current platform")
}

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit) = block()
