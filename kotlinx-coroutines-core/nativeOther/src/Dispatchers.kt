package kotlinx.coroutines

import kotlinx.coroutines.scheduling.DefaultScheduler
import kotlin.coroutines.*

internal actual fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher =
    MissingMainDispatcher

internal actual fun createDefaultDispatcher(): CoroutineDispatcher = DefaultScheduler

private object MissingMainDispatcher : MainCoroutineDispatcher() {
    override val immediate: MainCoroutineDispatcher
        get() = notImplemented()
    override fun dispatch(context: CoroutineContext, block: Runnable) = notImplemented()
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = notImplemented()
    override fun dispatchYield(context: CoroutineContext, block: Runnable) = notImplemented()

    private fun notImplemented(): Nothing = TODO("Dispatchers.Main is missing on the current platform")
}

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit) = block()
