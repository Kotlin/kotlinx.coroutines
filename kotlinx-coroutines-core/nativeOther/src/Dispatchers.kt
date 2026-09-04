package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.native.*

internal actual fun createMainDispatcherOrNull(): MainCoroutineDispatcher? = null

internal actual fun createDefaultDispatcher(): CoroutineDispatcher = DefaultDispatcher

private object DefaultDispatcher : CoroutineDispatcher() {
    // Be consistent with JVM -- at least 2 threads to provide some liveness guarantees in case of improper uses
    private val ctx = newFixedThreadPoolContext(Platform.getAvailableProcessors().coerceAtLeast(2), "Dispatchers.Default")

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        ctx.dispatch(context, block)
    }
}

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit) = block()
