package kotlinx.coroutines

import kotlin.coroutines.*

internal actual fun createEventLoop(): EventLoop = UnconfinedEventLoop()

internal actual fun nanoTime(): Long = unsupported()

internal class UnconfinedEventLoop : EventLoop() {
    override fun dispatch(context: CoroutineContext, block: Runnable): Unit = unsupported()
}

internal actual abstract class EventLoopImplPlatform : EventLoop() {
    protected actual fun unpark(): Unit = unsupported()
    protected actual fun reschedule(now: Long, delayedTask: EventLoopImplBase.DelayedTask): Unit = unsupported()
}

internal actual object DefaultExecutor {
    public actual fun enqueue(task: Runnable): Unit = unsupported()
}

private fun unsupported(): Nothing =
    throw UnsupportedOperationException("runBlocking event loop is not supported")

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit) = block()
