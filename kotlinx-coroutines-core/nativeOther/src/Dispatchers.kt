/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

internal actual fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher =
    NativeMainDispatcher(default)

private class NativeMainDispatcher(val delegate: CoroutineDispatcher) : MainCoroutineDispatcher() {
    override val immediate: MainCoroutineDispatcher
        get() = throw UnsupportedOperationException("Immediate dispatching is not supported on this platform")
    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.dispatch(context, block)
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.isDispatchNeeded(context)
    override fun dispatchYield(context: CoroutineContext, block: Runnable) = delegate.dispatchYield(context, block)
    override fun toString(): String = toStringInternalImpl() ?: delegate.toString()
}