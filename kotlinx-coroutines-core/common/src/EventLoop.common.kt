/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*

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
     * Queue used by [Dispatchers.Unconfined] tasks.
     * These tasks are thread-local for performance and take precedence over the rest of the queue.
     */
    private var unconfinedQueue: ArrayQueue<DispatchedTask<*>>? = null

    /**
     * Processes next event in this event loop.
     *
     * The result of this function is to be interpreted like this:
     * * `<= 0` -- there are potentially more events for immediate processing;
     * * `> 0` -- a number of nanoseconds to wait for next scheduled event;
     * * [Long.MAX_VALUE] -- no more events.
     *
     * **NOTE**: Must be invoked only from the event loop's thread
     *          (no check for performance reasons, may be added in the future).
     */
    public open fun processNextEvent(): Long {
        if (!processUnconfinedEvent()) return Long.MAX_VALUE
        return nextTime
    }

    protected open val isEmpty: Boolean get() = isUnconfinedQueueEmpty

    protected open val nextTime: Long
        get() {
            val queue = unconfinedQueue ?: return Long.MAX_VALUE
            return if (queue.isEmpty) Long.MAX_VALUE else 0L
        }

    public fun processUnconfinedEvent(): Boolean {
        val queue = unconfinedQueue ?: return false
        val task = queue.removeFirstOrNull() ?: return false
        task.run()
        return true
    }
    /**
     * Returns `true` if the invoking `runBlocking(context) { ... }` that was passed this event loop in its context
     * parameter should call [processNextEvent] for this event loop (otherwise, it will process thread-local one).
     * By default, event loop implementation is thread-local and should not processed in the context
     * (current thread's event loop should be processed instead).
     */
    public open fun shouldBeProcessedFromContext(): Boolean = false

    /**
     * Dispatches task whose dispatcher returned `false` from [CoroutineDispatcher.isDispatchNeeded]
     * into the current event loop.
     */
    public fun dispatchUnconfined(task: DispatchedTask<*>) {
        val queue = unconfinedQueue ?:
            ArrayQueue<DispatchedTask<*>>().also { unconfinedQueue = it }
        queue.addLast(task)
    }

    public val isActive: Boolean
        get() = useCount > 0

    public val isUnconfinedLoopActive: Boolean
        get() = useCount >= delta(unconfined = true)

    // May only be used from the event loop's thread
    public val isUnconfinedQueueEmpty: Boolean
        get() = unconfinedQueue?.isEmpty ?: true

    private fun delta(unconfined: Boolean) =
        if (unconfined) (1L shl 32) else 1L

    fun incrementUseCount(unconfined: Boolean = false) {
        useCount += delta(unconfined)
        if (!unconfined) shared = true 
    }

    fun decrementUseCount(unconfined: Boolean = false) {
        useCount -= delta(unconfined)
        if (useCount > 0) return
        check(useCount == 0L) { "Extra decrementUseCount" }
        if (shared) {
            // shut it down and remove from ThreadLocalEventLoop
            shutdown()
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

