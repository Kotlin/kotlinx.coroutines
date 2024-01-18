@file:OptIn(ObsoleteWorkersApi::class)

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.native.concurrent.*
import kotlin.system.*

internal actual abstract class EventLoopImplPlatform : EventLoop() {

    private val current = Worker.current

    protected actual fun unpark() {
        current.executeAfter(0L, {})// send an empty task to unpark the waiting event loop
    }

    protected actual fun reschedule(now: Long, delayedTask: EventLoopImplBase.DelayedTask) {
        DefaultExecutor.invokeOnTimeout(now, delayedTask, EmptyCoroutineContext)
    }
}

internal class EventLoopImpl: EventLoopImplBase() {
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        DefaultDelay.invokeOnTimeout(timeMillis, block, context)
}

internal actual fun createEventLoop(): EventLoop = EventLoopImpl()

@Suppress("DEPRECATION")
internal actual fun nanoTime(): Long = getTimeNanos()
