/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.multithreadingSupported
import kotlin.coroutines.*

public actual object Dispatchers {
    public actual val Default: CoroutineDispatcher = createDefaultDispatcherBasedOnMm()
    public actual val Main: MainCoroutineDispatcher
        get() = injectedMainDispatcher ?: mainDispatcher
    public actual val Unconfined: CoroutineDispatcher get() = kotlinx.coroutines.Unconfined // Avoid freezing

    private val mainDispatcher = createMainDispatcher(Default)

    private var injectedMainDispatcher: MainCoroutineDispatcher? = null

    @PublishedApi
    internal fun injectMain(dispatcher: MainCoroutineDispatcher) {
        if (!multithreadingSupported) {
            throw IllegalStateException("Dispatchers.setMain is not supported in Kotlin/Native when new memory model is disabled")
        }
        injectedMainDispatcher = dispatcher
    }

    @PublishedApi
    internal fun resetInjectedMain() {
        injectedMainDispatcher = null
    }
}

internal expect fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher

private fun createDefaultDispatcherBasedOnMm(): CoroutineDispatcher {
    return if (multithreadingSupported) createDefaultDispatcher()
    else OldDefaultExecutor
}

private fun takeEventLoop(): EventLoopImpl =
    ThreadLocalEventLoop.currentOrNull() as? EventLoopImpl ?:
    error("There is no event loop. Use runBlocking { ... } to start one.")

internal object OldDefaultExecutor : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) =
        takeEventLoop().dispatch(context, block)
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        takeEventLoop().scheduleResumeAfterDelay(timeMillis, continuation)
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        takeEventLoop().invokeOnTimeout(timeMillis, block, context)
}

internal class OldMainDispatcher(private val delegate: CoroutineDispatcher) : MainCoroutineDispatcher() {
    override val immediate: MainCoroutineDispatcher
        get() = throw UnsupportedOperationException("Immediate dispatching is not supported on Native")
    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.dispatch(context, block)
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.isDispatchNeeded(context)
    override fun dispatchYield(context: CoroutineContext, block: Runnable) = delegate.dispatchYield(context, block)
    override fun toString(): String = toStringInternalImpl() ?: delegate.toString()
}
