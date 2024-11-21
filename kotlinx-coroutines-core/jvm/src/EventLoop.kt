package kotlinx.coroutines

internal actual abstract class EventLoopImplPlatform: EventLoop() {
    /** Returns `null` if a thread was created and doesn't need to be awoken.
     * Returns a thread to awaken if the thread already existed when this method was called. */
    protected abstract fun startThreadOrObtainSleepingThread(): Thread?

    protected actual fun unpark() {
        startThreadOrObtainSleepingThread()?.let(::unpark)
    }

}

internal class BlockingEventLoop(
    private val thread: Thread
) : EventLoopImplBase() {
    override fun startThreadOrObtainSleepingThread(): Thread? =
        if (Thread.currentThread() !== thread) thread else null

}

internal actual fun createEventLoop(): EventLoop = BlockingEventLoop(Thread.currentThread())

internal actual inline fun platformAutoreleasePool(crossinline block: () -> Unit) = block()
