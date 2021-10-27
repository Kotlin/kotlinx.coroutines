/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

internal actual fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher =
    MissingMainDispatcher

internal actual fun createDefaultDispatcher(): CoroutineDispatcher = DefaultDispatcher

private object DefaultDispatcher : CoroutineDispatcher() {

    // Delegated, so users won't be able to downcast and call 'close'
    // The precise number of threads cannot be obtained until KT-48179 is implemented, 4 is just "good enough" number.
    private val ctx = newFixedThreadPoolContext(4, "Dispatchers.Default")

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
