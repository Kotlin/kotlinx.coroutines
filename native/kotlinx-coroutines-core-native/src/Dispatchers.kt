/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*


actual object Dispatchers {

    public actual val Default: CoroutineDispatcher = createDefaultDispatcher()

    public actual val Main: MainCoroutineDispatcher = NativeMainDispatcher(Default)

    public actual val Unconfined: CoroutineDispatcher = kotlinx.coroutines.experimental.Unconfined
}

private class NativeMainDispatcher(val delegate: CoroutineDispatcher) : MainCoroutineDispatcher() {

    override val immediate: MainCoroutineDispatcher
        get() = throw UnsupportedOperationException("Immediate dispatching is not supported on Native")

    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.dispatch(context, block)

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.isDispatchNeeded(context)

    override fun dispatchYield(context: CoroutineContext, block: Runnable) = delegate.dispatchYield(context, block)

    override fun toString(): String = delegate.toString()
}
