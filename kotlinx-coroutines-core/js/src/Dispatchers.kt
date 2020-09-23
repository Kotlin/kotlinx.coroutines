/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

public actual object Dispatchers {
    public actual val Default: CoroutineDispatcher = createDefaultDispatcher()
    public actual val Main: MainCoroutineDispatcher = JsMainDispatcher(Default, false)
    public actual val Unconfined: CoroutineDispatcher = kotlinx.coroutines.Unconfined
}

private class JsMainDispatcher(
    val delegate: CoroutineDispatcher,
    private val invokeImmediately: Boolean
) : MainCoroutineDispatcher() {
    override val immediate: MainCoroutineDispatcher =
        if (invokeImmediately) this else JsMainDispatcher(delegate, true)
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = !invokeImmediately
    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.dispatch(context, block)
    override fun dispatchYield(context: CoroutineContext, block: Runnable) = delegate.dispatchYield(context, block)
    override fun toString(): String = toStringInternalImpl() ?: delegate.toString()
}
