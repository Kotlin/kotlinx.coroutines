/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.multithreadingSupported
import kotlin.coroutines.*

internal actual fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher =
    MissingMainDispatcher

private object MissingMainDispatcher : MainCoroutineDispatcher() {
    override val immediate: MainCoroutineDispatcher
        get() = notImplemented()
    override fun dispatch(context: CoroutineContext, block: Runnable) = notImplemented()
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = notImplemented()
    override fun dispatchYield(context: CoroutineContext, block: Runnable) = notImplemented()

    private fun notImplemented(): Nothing = TODO("Dispatchers.Main is missing on the current platform")
}
