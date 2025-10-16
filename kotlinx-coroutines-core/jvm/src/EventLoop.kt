package kotlinx.coroutines

internal actual abstract class EventLoopImplPlatform: EventLoop() {

    protected abstract val thread: Thread

    protected actual fun unpark() {
        val thread = thread // atomic read
        if (Thread.currentThread() !== thread)
            unpark(thread)
    }

    protected actual open fun reschedule(now: Long, delayedTask: EventLoopImplBase.DelayedTask) {
        DefaultExecutor.schedule(now, delayedTask)
    }
}

internal class BlockingEventLoop(
    override val thread: Thread
) : EventLoopImplBase()

internal actual fun createEventLoop(): EventLoop = BlockingEventLoop(Thread.currentThread())

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit) = block()
