/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

/** Not inside [Dispatchers], as otherwise mutating this throws an `InvalidMutabilityException`. */
private var injectedMainDispatcher: MainCoroutineDispatcher? = null

public actual object Dispatchers {
    public actual val Default: CoroutineDispatcher = createDefaultDispatcher()
    public actual val Main: MainCoroutineDispatcher
        get() = injectedMainDispatcher ?: mainDispatcher
    public actual val Unconfined: CoroutineDispatcher get() = kotlinx.coroutines.Unconfined // Avoid freezing

    private val mainDispatcher = NativeMainDispatcher(Default)

    @PublishedApi
    internal fun injectMain(dispatcher: MainCoroutineDispatcher) {
        injectedMainDispatcher = dispatcher
    }

    @PublishedApi
    internal fun resetInjectedMain() {
        injectedMainDispatcher = null
    }
}

private class NativeMainDispatcher(val delegate: CoroutineDispatcher) : MainCoroutineDispatcher() {
    override val immediate: MainCoroutineDispatcher
        get() = throw UnsupportedOperationException("Immediate dispatching is not supported on Native")
    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.dispatch(context, block)
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.isDispatchNeeded(context)
    override fun dispatchYield(context: CoroutineContext, block: Runnable) = delegate.dispatchYield(context, block)
    override fun toString(): String = toStringInternalImpl() ?: delegate.toString()
}
