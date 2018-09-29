/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.internal.*
import java.util.concurrent.locks.*
import kotlin.coroutines.experimental.*

/**
 * Implemented by [CoroutineDispatcher] implementations that have event loop inside and can
 * be asked to process next event from their event queue.
 *
 * It may optionally implement [Delay] interface and support time-scheduled tasks. It is used by [runBlocking] to
 * continue processing events when invoked from the event dispatch thread.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi // todo: review KDoc references to this interface
public interface EventLoop: ContinuationInterceptor {
    /**
     * Processes next event in this event loop.
     *
     * The result of this function is to be interpreted like this:
     * * `<= 0` -- there are potentially more events for immediate processing;
     * * `> 0` -- a number of nanoseconds to wait for next scheduled event;
     * * [Long.MAX_VALUE] -- no more events, or was invoked from the wrong thread.
     */
    public fun processNextEvent(): Long

    /** @suppress **Deprecated **/
    @Deprecated(message = "Companion object to be removed, no replacement")
    public companion object Factory {
        /** @suppress **Deprecated **/
        @Deprecated("Replaced with top-level function", level = DeprecationLevel.HIDDEN)
        public operator fun invoke(thread: Thread = Thread.currentThread(), parentJob: Job? = null): CoroutineDispatcher =
            EventLoopImpl(thread).apply {
                if (parentJob != null) initParentJob(parentJob)
            }
    }
}

/**
 * Creates a new event loop that is bound the specified [thread] (current thread by default) and
 * stops accepting new events when [parentJob] completes. Every continuation that is scheduled
 * onto this event loop unparks the specified thread via [LockSupport.unpark].
 *
 * The main event-processing loop using the resulting `eventLoop` object should look like this:
 * ```
 * while (needsToBeRunning) {
 *     if (Thread.interrupted()) break // or handle somehow
 *     LockSupport.parkNanos(eventLoop.processNextEvent()) // event loop will unpark
 * }
 * ```
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@Suppress("FunctionName")
@InternalCoroutinesApi
public fun EventLoop(thread: Thread = Thread.currentThread(), parentJob: Job? = null): EventLoop =
    EventLoopImpl(thread).apply {
        if (parentJob != null) initParentJob(parentJob)
    }

/**
 * @suppress **Deprecated**: Preserves binary compatibility with old code
 */
@JvmName("EventLoop")
@Deprecated(level = DeprecationLevel.HIDDEN, message = "Preserves binary compatibility with old code")
public fun EventLoop_Deprecated(thread: Thread = Thread.currentThread(), parentJob: Job? = null): CoroutineDispatcher =
    EventLoop(thread, parentJob) as CoroutineDispatcher

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

@Suppress("PrivatePropertyName")
private val CLOSED_EMPTY = Symbol("CLOSED_EMPTY")

private typealias Queue<T> = LockFreeMPSCQueueCore<T>

internal abstract class EventLoopBase: CoroutineDispatcher(), Delay, EventLoop {
    // null | CLOSED_EMPTY | task | Queue<Runnable>
    private val _queue = atomic<Any?>(null)

    // Allocated only only once
    private val _delayed = atomic<ThreadSafeHeap<DelayedTask>?>(null)

    protected abstract val isCompleted: Boolean
    protected abstract fun unpark()
    protected abstract fun isCorrectThread(): Boolean

    protected val isEmpty: Boolean
        get() = isQueueEmpty && isDelayedEmpty

    private val isQueueEmpty: Boolean get() {
        val queue = _queue.value
        return when (queue) {
            null -> true
            is Queue<*> -> queue.isEmpty
            else -> queue === CLOSED_EMPTY
        }
    }

    private val isDelayedEmpty: Boolean get() {
        val delayed = _delayed.value
        return delayed == null || delayed.isEmpty
    }

    private val nextTime: Long
        get() {
            val queue = _queue.value
            when {
                queue === null -> {} // empty queue -- proceed
                queue is Queue<*> -> if (!queue.isEmpty) return 0 // non-empty queue
                queue === CLOSED_EMPTY -> return Long.MAX_VALUE // no more events -- closed
                else -> return 0 // non-empty queue
            }
            val delayed = _delayed.value ?: return Long.MAX_VALUE
            val nextDelayedTask = delayed.peek() ?: return Long.MAX_VALUE
            return (nextDelayedTask.nanoTime - timeSource.nanoTime()).coerceAtLeast(0)
        }

    override fun dispatch(context: CoroutineContext, block: Runnable) =
        execute(block)

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        schedule(DelayedResumeTask(timeMillis, continuation))

    override fun processNextEvent(): Long {
        if (!isCorrectThread()) return Long.MAX_VALUE
        // queue all delayed tasks that are due to be executed
        val delayed = _delayed.value
        if (delayed != null && !delayed.isEmpty) {
            val now = timeSource.nanoTime()
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

    internal fun execute(task: Runnable) {
        if (enqueueImpl(task)) {
            // todo: we should unpark only when this delayed task became first in the queue
            unpark()
        } else {
            DefaultExecutor.execute(task)
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
                        val newQueue = Queue<Runnable>(Queue.INITIAL_CAPACITY)
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

    protected fun closeQueue() {
        assert(isCompleted)
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
                        val newQueue = Queue<Runnable>(Queue.INITIAL_CAPACITY)
                        newQueue.addLast(queue as Runnable)
                        if (_queue.compareAndSet(queue, newQueue)) return
                    }
                }
            }
        }

    }

    internal fun schedule(delayedTask: DelayedTask) {
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
        return delayedTask.schedule(delayed)
    }

    internal fun removeDelayedImpl(delayedTask: DelayedTask) {
        _delayed.value?.remove(delayedTask)
    }

    // It performs "hard" shutdown for test cleanup purposes
    protected fun resetAll() {
        _queue.value = null
        _delayed.value = null
    }

    // This is a "soft" (normal) shutdown
    protected fun rescheduleAllDelayed() {
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

    internal abstract inner class DelayedTask(
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
        
        @JvmField val nanoTime: Long = timeSource.nanoTime() + delayToNanos(timeMillis)

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
        fun schedule(delayed: ThreadSafeHeap<DelayedTask>): Int {
            if (_heap === DISPOSED_TASK) return SCHEDULE_DISPOSED // don't add -- was already disposed
            return if (delayed.addLastIf(this) { !isCompleted }) SCHEDULE_OK else SCHEDULE_COMPLETED
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

    // Cannot be moved to DefaultExecutor due to BE bug
    internal inner class DelayedRunnableTask(
        time: Long,
        private val block: Runnable
    ) : DelayedTask(time) {
        override fun run() { block.run() }
        override fun toString(): String = super.toString() + block.toString()
    }
}

internal abstract class ThreadEventLoop(
    private val thread: Thread
) : EventLoopBase() {
    override fun isCorrectThread(): Boolean = Thread.currentThread() === thread

    override fun unpark() {
        if (Thread.currentThread() !== thread)
            timeSource.unpark(thread)
    }

    fun shutdown() {
        closeQueue()
        assert(isCorrectThread())
        // complete processing of all queued tasks
        while (processNextEvent() <= 0) { /* spin */ }
        // reschedule the rest of delayed tasks
        rescheduleAllDelayed()
    }
}

private class EventLoopImpl(thread: Thread) : ThreadEventLoop(thread) {
    private var parentJob: Job? = null

    override val isCompleted: Boolean get() = parentJob?.isCompleted == true

    fun initParentJob(parentJob: Job) {
        require(this.parentJob == null)
        this.parentJob = parentJob
    }
}

internal class BlockingEventLoop(thread: Thread) : ThreadEventLoop(thread) {
    @Volatile
    public override var isCompleted: Boolean = false
}
