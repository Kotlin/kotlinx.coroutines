@file:OptIn(ObsoleteWorkersApi::class)

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.native.concurrent.*

internal actual fun <T> runBlockingImpl(
    newContext: CoroutineContext, eventLoop: EventLoop?, block: suspend CoroutineScope.() -> T
): T {
    val coroutine = BlockingCoroutine<T>(newContext, Worker.current, eventLoop)
    ThreadLocalKeepAlive.registerUsage()
    try {
        coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
        return coroutine.joinBlocking()
    } finally {
        ThreadLocalKeepAlive.unregisterUsage()
    }
}

@ThreadLocal
private object ThreadLocalKeepAlive {
    /** If larger than 0, this means this [Worker] is still used. */
    private var usages = 0

    /** Whether the worker currently tries to keep itself alive. */
    private var keepAliveLoopActive = false

    /** Ensure that the worker is kept alive until the matching [unregisterUsage] is called. */
    fun registerUsage() {
        usages++
        if (!keepAliveLoopActive) keepAlive()
    }

    /** Undo [registerUsage]. */
    fun unregisterUsage() {
        usages--
    }

    /**
     * Send a ping to the worker to prevent it from terminating while this coroutine is running,
     * ensuring that continuations don't get dropped and forgotten.
     */
    private fun keepAlive() {
        // if there are no checks left, we no longer keep the worker alive, it can be terminated
        keepAliveLoopActive = usages > 0
        if (keepAliveLoopActive) {
            Worker.current.executeAfter(afterMicroseconds = 100_000) {
                keepAlive()
            }
        }
    }
}

private class BlockingCoroutine<T>(
    parentContext: CoroutineContext,
    private val joinWorker: Worker,
    private val eventLoop: EventLoop?
) : AbstractCoroutine<T>(parentContext, true, true) {

    override val isScopedCoroutine: Boolean get() = true

    override fun afterCompletion(state: Any?) {
        // wake up blocked thread
        if (joinWorker != Worker.current) {
            // Unpark waiting worker
            joinWorker.executeAfter(0L, {}) // send an empty task to unpark the waiting event loop
        }
    }

    @Suppress("UNCHECKED_CAST")
    fun joinBlocking(): T {
        try {
            eventLoop?.incrementUseCount()
            while (true) {
                var parkNanos: Long
                // Workaround for bug in BE optimizer that cannot eliminate boxing here
                if (eventLoop != null) {
                    parkNanos = eventLoop.processNextEvent()
                } else {
                    parkNanos = Long.MAX_VALUE
                }
                // note: processNextEvent may lose unpark flag, so check if completed before parking
                if (isCompleted) break
                joinWorker.park(parkNanos / 1000L, true)
            }
        } finally { // paranoia
            eventLoop?.decrementUseCount()
        }
        // now return result
        val state = state.unboxState()
        (state as? CompletedExceptionally)?.let { throw it.cause }
        return state as T
    }
}
