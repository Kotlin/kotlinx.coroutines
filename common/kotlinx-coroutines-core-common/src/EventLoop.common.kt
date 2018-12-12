/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * Extended by [CoroutineDispatcher] implementations that have event loop inside and can
 * be asked to process next event from their event queue.
 *
 * It may optionally implement [Delay] interface and support time-scheduled tasks.
 * It is created or pigged back onto (see [ThreadLocalEventLoop])
 * by [runBlocking] and by [Dispatchers.Unconfined].
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
internal abstract class EventLoop : CoroutineDispatcher() {
    /**
     * Processes next event in this event loop.
     *
     * The result of this function is to be interpreted like this:
     * * `<= 0` -- there are potentially more events for immediate processing;
     * * `> 0` -- a number of nanoseconds to wait for next scheduled event;
     * * [Long.MAX_VALUE] -- no more events, or was invoked from the wrong thread.
     */
    public abstract fun processNextEvent(): Long

    public abstract val isEmpty: Boolean

    /**
     * Dispatches task whose dispatcher returned `false` from [CoroutineDispatcher.isDispatchNeeded]
     * into the current event loop.
     */
    public fun dispatchUnconfined(task: DispatchedTask<*>) {
        task.isUnconfinedTask = true
        check(enqueue(task)) { "Attempting to dispatchUnconfined into the EventLoop that was shut down"}
        queuedUnconfinedTasks++
    }

    public override fun dispatch(context: CoroutineContext, block: Runnable) {
        if (block is DispatchedTask<*>) block.isUnconfinedTask = false
        enqueue(block)
    }

    // returns true if it was successfully enqueued for execution in this event loop, false if got to default executor
    public abstract fun enqueue(task: Runnable): Boolean

    protected fun runBlock(block: Runnable) {
        try {
            block.run()
        } finally {
            if (block is DispatchedTask<*> && block.isUnconfinedTask) {
                check(--queuedUnconfinedTasks >= 0) { "queuedUnconfinedTasks underflow" }
            }
        }
    }

    /**
     * Counts the number of nested [runBlocking] and [Dispatchers.Unconfined] that use this event loop.
     */
    private var useCount = 0L

    /**
     * Set to true on any use by [runBlocking], because it potentially leaks this loop to other threads, so
     * this instance must be properly shutdown. We don't need to shutdown event loop that was used solely
     * by [Dispatchers.Unconfined] -- it can be left as [ThreadLocalEventLoop] and reused next time.
     */
    private var shared = false

    /**
     * Counts a number of currently enqueued (but not executed yet) unconfined tasks.
     */
    private var queuedUnconfinedTasks = 0

    public val isActive: Boolean
        get() = useCount > 0

    public val isUnconfinedLoopActive: Boolean
        get() = useCount >= increment(unconfined = true)

    public val isEmptyUnconfinedQueue: Boolean
        get() = queuedUnconfinedTasks == 0

    private fun increment(unconfined: Boolean) =
        if (unconfined) (1L shl 32) else 1L

    fun incrementUseCount(unconfined: Boolean = false) {
        useCount += increment(unconfined)
        if (!unconfined) shared = true 
    }

    fun decrementUseCount(unconfined: Boolean = false) {
        useCount -= increment(unconfined)
        if (useCount > 0) return
        check(useCount == 0L) { "Extra decrementUseCount" }
        if (shared) {
            // shut it down and remove from ThreadLocalEventLoop
            shutdown()
        } else {
            // it was not shared, so it could not have accumulated any other tasks
            check(isEmpty) { "EventLoop that was used only by unconfined tasks should be empty" }
        }
    }

    protected open fun shutdown() {}
}

@NativeThreadLocal
internal object ThreadLocalEventLoop {
    private val ref = CommonThreadLocal<EventLoop?>()

    internal val eventLoop: EventLoop
        get() = ref.get() ?: createEventLoop().also { ref.set(it) }

    internal fun currentOrNull(): EventLoop? =
        ref.get()

    internal fun resetEventLoop() {
        ref.set(null)
    }

    internal fun setEventLoop(eventLoop: EventLoop) {
        ref.set(eventLoop)
    }
}

internal expect fun createEventLoop(): EventLoop

