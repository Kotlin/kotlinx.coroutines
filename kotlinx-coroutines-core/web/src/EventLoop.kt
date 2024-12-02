package kotlinx.coroutines

import kotlin.coroutines.*

internal actual fun createEventLoop(): EventLoop = UnconfinedEventLoopImpl()

internal actual fun nanoTime(): Long = unsupported()

private class UnconfinedEventLoopImpl : EventLoop() {
    override fun dispatch(context: CoroutineContext, block: Runnable): Unit = unsupported()
}

internal actual abstract class EventLoopImplPlatform : EventLoop() {
    protected actual fun unpark(): Unit = unsupported()
}

private fun unsupported(): Nothing =
    throw UnsupportedOperationException("runBlocking event loop is not supported")

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit) = block()

internal actual fun rescheduleTaskFromClosedDispatcher(task: Runnable) {
    Dispatchers.Default.dispatch(Dispatchers.Default, task)
}
