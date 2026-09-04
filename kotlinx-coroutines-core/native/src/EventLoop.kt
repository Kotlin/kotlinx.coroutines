@file:OptIn(ObsoleteWorkersApi::class)

package kotlinx.coroutines

import kotlin.native.concurrent.*
import kotlin.time.*

internal actual abstract class EventLoopImplPlatform : EventLoop() {
    /** Returns `null` if a thread was created and doesn't need to be awoken.
     * Returns a thread to awaken if the thread already existed when this method was called. */
    protected abstract fun startThreadOrObtainSleepingThread(): Worker?

    protected actual fun unpark() {
        startThreadOrObtainSleepingThread()?.let {
            it.executeAfter(0L) {} // send an empty task to unpark the waiting event loop
        }
    }
}

internal class BlockingEventLoop(
    private val worker: Worker
) : EventLoopImplBase() {
    override fun startThreadOrObtainSleepingThread(): Worker? =
        if (Worker.current.id != worker.id) worker else null
}

internal actual fun createEventLoop(): EventLoop = BlockingEventLoop(Worker.current)

private val startingPoint = TimeSource.Monotonic.markNow()

internal actual fun nanoTime(): Long = (TimeSource.Monotonic.markNow() - startingPoint).inWholeNanoseconds
