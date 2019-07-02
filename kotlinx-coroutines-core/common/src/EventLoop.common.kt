/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

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
        assert { useCount == 0L } // "Extra decrementUseCount"
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

@SharedImmutable
private val DISPOSED_TASK = Symbol("REMOVED_TASK")

// results for scheduleImpl
private const val SCHEDULE_OK = 0
private const val SCHEDULE_COMPLETED = 1
private const val SCHEDULE_DISPOSED = 2

private const val MS_TO_NS = 1_000_000L
private const val MAX_MS = Long.MAX_VALUE / MS_TO_NS

internal fun delayToNanos(timeMillis: Long): Long = when {
    timeMillis <= 0 -> 0L
    timeMillis >= MAX_MS -> Long.MAX_VALUE
    else -> timeMillis * MS_TO_NS
}

internal fun delayNanosToMillis(timeNanos: Long): Long =
    timeNanos / MS_TO_NS

@SharedImmutable
private val CLOSED_EMPTY = Symbol("CLOSED_EMPTY")

private typealias Queue<T> = LockFreeTaskQueueCore<T>

internal expect abstract class EventLoopImplPlatform() : EventLoop {
    protected fun unpark()
}

internal abstract class EventLoopImplBase: EventLoopImplPlatform(), Delay {
    // null | CLOSED_EMPTY | task | Queue<Runnable>
    private val _queue = atomic<Any?>(null)

    // Allocated only only once
    private val _delayed = atomic<ThreadSafeHeap<DelayedTask>?>(null)

    @Volatile
    private var isCompleted = false

    override val isEmpty: Boolean get() {
        if (!isUnconfinedQueueEmpty) return false
        val delayed = _delayed.value
        if (delayed != null && !delayed.isEmpty) return false
        val queue = _queue.value
        return when (queue) {
            null -> true
            is Queue<*> -> queue.isEmpty
            else -> queue === CLOSED_EMPTY
        }
    }

    protected override val nextTime: Long
        get() {
            if (super.nextTime == 0L) return 0L
            val queue = _queue.value
            when {
                queue === null -> {} // empty queue -- proceed
                queue is Queue<*> -> if (!queue.isEmpty) return 0 // non-empty queue
                queue === CLOSED_EMPTY -> return Long.MAX_VALUE // no more events -- closed
                else -> return 0 // non-empty queue
            }
            val delayed = _delayed.value ?: return Long.MAX_VALUE
            val nextDelayedTask = delayed.peek() ?: return Long.MAX_VALUE
            return (nextDelayedTask.nanoTime - nanoTime()).coerceAtLeast(0)
        }

    override fun shutdown() {
        // Clean up thread-local reference here -- this event loop is shutting down
        ThreadLocalEventLoop.resetEventLoop()
        // We should signal that this event loop should not accept any more tasks
        // and process queued events (that could have been added after last processNextEvent)
        isCompleted = true
        closeQueue()
        // complete processing of all queued tasks
        while (processNextEvent() <= 0) { /* spin */ }
        // reschedule the rest of delayed tasks
        rescheduleAllDelayed()
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        schedule(DelayedResumeTask(timeMillis, continuation))

    override fun processNextEvent(): Long {
        // unconfined events take priority
        if (processUnconfinedEvent()) return nextTime
        // queue all delayed tasks that are due to be executed
        val delayed = _delayed.value
        if (delayed != null && !delayed.isEmpty) {
            val now = nanoTime()
            while (true) {
                // make sure that moving from delayed to queue removes from delayed only after it is added to queue
                // to make sure that 'isEmpty' and `nextTime` that check both of them
                // do not transiently report that both delayed and queue are empty during move
                delayed.removeFirstIf {
                    if (it.timeToExecute(now)) {
                        enqueueImpl(it)
                    } else
                        false
                } ?: break // quit loop when nothing more to remove or enqueueImpl returns false on "isComplete"
            }
        }
        // then process one event from queue
        dequeue()?.run()
        return nextTime
    }

    public final override fun dispatch(context: CoroutineContext, block: Runnable) = enqueue(block)

    public fun enqueue(task: Runnable) {
        if (enqueueImpl(task)) {
            // todo: we should unpark only when this delayed task became first in the queue
            unpark()
        } else {
            DefaultExecutor.enqueue(task)
        }
    }

    @Suppress("UNCHECKED_CAST")
    private fun enqueueImpl(task: Runnable): Boolean {
        _queue.loop { queue ->
            if (isCompleted) return false // fail fast if already completed, may still add, but queues will close
            when (queue) {
                null -> if (_queue.compareAndSet(null, task)) return true
                is Queue<*> -> {
                    when ((queue as Queue<Runnable>).addLast(task)) {
                        Queue.ADD_SUCCESS -> return true
                        Queue.ADD_CLOSED -> return false
                        Queue.ADD_FROZEN -> _queue.compareAndSet(queue, queue.next())
                    }
                }
                else -> when {
                    queue === CLOSED_EMPTY -> return false
                    else -> {
                        // update to full-blown queue to add one more
                        val newQueue = Queue<Runnable>(Queue.INITIAL_CAPACITY, singleConsumer = true)
                        newQueue.addLast(queue as Runnable)
                        newQueue.addLast(task)
                        if (_queue.compareAndSet(queue, newQueue)) return true
                    }
                }
            }
        }
    }

    @Suppress("UNCHECKED_CAST")
    private fun dequeue(): Runnable? {
        _queue.loop { queue ->
            when (queue) {
                null -> return null
                is Queue<*> -> {
                    val result = (queue as Queue<Runnable>).removeFirstOrNull()
                    if (result !== Queue.REMOVE_FROZEN) return result as Runnable?
                    _queue.compareAndSet(queue, queue.next())
                }
                else -> when {
                    queue === CLOSED_EMPTY -> return null
                    else -> if (_queue.compareAndSet(queue, null)) return queue as Runnable
                }
            }
        }
    }

    private fun closeQueue() {
        assert { isCompleted }
        _queue.loop { queue ->
            when (queue) {
                null -> if (_queue.compareAndSet(null, CLOSED_EMPTY)) return
                is Queue<*> -> {
                    queue.close()
                    return
                }
                else -> when {
                    queue === CLOSED_EMPTY -> return
                    else -> {
                        // update to full-blown queue to close
                        val newQueue = Queue<Runnable>(Queue.INITIAL_CAPACITY, singleConsumer = true)
                        newQueue.addLast(queue as Runnable)
                        if (_queue.compareAndSet(queue, newQueue)) return
                    }
                }
            }
        }

    }

    public fun schedule(delayedTask: DelayedTask) {
        when (scheduleImpl(delayedTask)) {
            SCHEDULE_OK -> if (shouldUnpark(delayedTask)) unpark()
            SCHEDULE_COMPLETED -> DefaultExecutor.schedule(delayedTask)
            SCHEDULE_DISPOSED -> {} // do nothing -- task was already disposed
            else -> error("unexpected result")
        }
    }

    private fun shouldUnpark(task: DelayedTask): Boolean = _delayed.value?.peek() === task

    private fun scheduleImpl(delayedTask: DelayedTask): Int {
        if (isCompleted) return SCHEDULE_COMPLETED
        val delayed = _delayed.value ?: run {
            _delayed.compareAndSet(null, ThreadSafeHeap())
            _delayed.value!!
        }
        return delayedTask.schedule(delayed, this)
    }

    // It performs "hard" shutdown for test cleanup purposes
    protected fun resetAll() {
        _queue.value = null
        _delayed.value = null
    }

    // This is a "soft" (normal) shutdown
    private fun rescheduleAllDelayed() {
        while (true) {
            /*
             * `removeFirstOrNull` below is the only operation on DelayedTask & ThreadSafeHeap that is not
             * synchronized on DelayedTask itself. All other operation are synchronized both on
             * DelayedTask & ThreadSafeHeap instances (in this order). It is still safe, because `dispose`
             * first removes DelayedTask from the heap (under synchronization) then
             * assign "_heap = DISPOSED_TASK", so there cannot be ever a race to _heap reference update.
             */
            val delayedTask = _delayed.value?.removeFirstOrNull() ?: break
            delayedTask.rescheduleOnShutdown()
        }
    }

    internal abstract class DelayedTask(
        timeMillis: Long
    ) : Runnable, Comparable<DelayedTask>, DisposableHandle, ThreadSafeHeapNode {
        private var _heap: Any? = null // null | ThreadSafeHeap | DISPOSED_TASK

        override var heap: ThreadSafeHeap<*>?
            get() = _heap as? ThreadSafeHeap<*>
            set(value) {
                require(_heap !== DISPOSED_TASK) // this can never happen, it is always checked before adding/removing
                _heap = value
            }

        override var index: Int = -1

        @JvmField val nanoTime: Long = nanoTime() + delayToNanos(timeMillis)

        override fun compareTo(other: DelayedTask): Int {
            val dTime = nanoTime - other.nanoTime
            return when {
                dTime > 0 -> 1
                dTime < 0 -> -1
                else -> 0
            }
        }

        fun timeToExecute(now: Long): Boolean = now - nanoTime >= 0L

        @Synchronized
        fun schedule(delayed: ThreadSafeHeap<DelayedTask>, eventLoop: EventLoopImplBase): Int {
            if (_heap === DISPOSED_TASK) return SCHEDULE_DISPOSED // don't add -- was already disposed
            return if (delayed.addLastIf(this) { !eventLoop.isCompleted }) SCHEDULE_OK else SCHEDULE_COMPLETED
        }

        // note: DefaultExecutor.schedule performs `schedule` (above) which does sync & checks for DISPOSED_TASK
        fun rescheduleOnShutdown() = DefaultExecutor.schedule(this)

        @Synchronized
        final override fun dispose() {
            val heap = _heap
            if (heap === DISPOSED_TASK) return // already disposed
            @Suppress("UNCHECKED_CAST")
            (heap as? ThreadSafeHeap<DelayedTask>)?.remove(this) // remove if it is in heap (first)
            _heap = DISPOSED_TASK // never add again to any heap
        }

        override fun toString(): String = "Delayed[nanos=$nanoTime]"
    }

    private inner class DelayedResumeTask(
        timeMillis: Long,
        private val cont: CancellableContinuation<Unit>
    ) : DelayedTask(timeMillis) {
        init {
            // Note that this operation isn't lock-free, but very short
            cont.disposeOnCancellation(this)
        }

        override fun run() {
            with(cont) { resumeUndispatched(Unit) }
        }
    }

    internal class DelayedRunnableTask(
        time: Long,
        private val block: Runnable
    ) : DelayedTask(time) {
        override fun run() { block.run() }
        override fun toString(): String = super.toString() + block.toString()
    }
}

internal expect fun createEventLoop(): EventLoop

internal expect fun nanoTime(): Long

internal expect object DefaultExecutor {
    public fun enqueue(task: Runnable)
    public fun schedule(delayedTask: EventLoopImplBase.DelayedTask)
}

