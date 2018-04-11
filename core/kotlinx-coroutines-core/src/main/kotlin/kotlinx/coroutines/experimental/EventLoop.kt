/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.internal.*
import kotlinx.coroutines.experimental.timeunit.TimeUnit
import java.util.concurrent.locks.*
import kotlin.coroutines.experimental.*

/**
 * Implemented by [CoroutineDispatcher] implementations that have event loop inside and can
 * be asked to process next event from their event queue.
 *
 * It may optionally implement [Delay] interface and support time-scheduled tasks. It is used by [runBlocking] to
 * continue processing events when invoked from the event dispatch thread.
 */
public interface EventLoop {
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
 */
@Suppress("FunctionName")
public fun EventLoop(thread: Thread = Thread.currentThread(), parentJob: Job? = null): CoroutineDispatcher =
    EventLoopImpl(thread).apply {
        if (parentJob != null) initParentJob(parentJob)
    }

private const val DELAYED = 0
private const val REMOVED = 1
private const val RESCHEDULED = 2

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
            if (!isQueueEmpty) return 0
            val delayed = _delayed.value ?: return Long.MAX_VALUE
            val nextDelayedTask = delayed.peek() ?: return Long.MAX_VALUE
            return (nextDelayedTask.nanoTime - timeSource.nanoTime()).coerceAtLeast(0)
        }

    override fun dispatch(context: CoroutineContext, block: Runnable) =
        execute(block)

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) =
        schedule(DelayedResumeTask(time, unit, continuation))

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle =
        DelayedRunnableTask(time, unit, block).also { schedule(it) }

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

    @Suppress("MemberVisibilityCanBePrivate") // todo: remove suppress when KT-22030 is fixed
    internal fun execute(task: Runnable) {
        if (enqueueImpl(task)) {
            // todo: we should unpark only when this delayed task became first in the queue
            unpark()
        } else
            DefaultExecutor.execute(task)
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
        if (scheduleImpl(delayedTask)) {
            // todo: we should unpark only when this delayed task became first in the queue
            unpark()
        } else
            DefaultExecutor.schedule(delayedTask)
    }

    private fun scheduleImpl(delayedTask: DelayedTask): Boolean {
        if (isCompleted) return false
        val delayed = _delayed.value ?: run {
            _delayed.compareAndSet(null, ThreadSafeHeap())
            _delayed.value!!
        }
        return delayed.addLastIf(delayedTask) { !isCompleted }
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
            val delayedTask = _delayed.value?.removeFirstOrNull() ?: break
            delayedTask.rescheduleOnShutdown()
        }
    }

    internal abstract inner class DelayedTask(
        time: Long, timeUnit: TimeUnit
    ) : Runnable, Comparable<DelayedTask>, DisposableHandle, ThreadSafeHeapNode {
        override var index: Int = -1
        var state = DELAYED // Guarded by by lock on this task for reschedule/dispose purposes
        @JvmField val nanoTime: Long = timeSource.nanoTime() + timeUnit.toNanos(time)

        override fun compareTo(other: DelayedTask): Int {
            val dTime = nanoTime - other.nanoTime
            return when {
                dTime > 0 -> 1
                dTime < 0 -> -1
                else -> 0
            }
        }

        fun timeToExecute(now: Long): Boolean = now - nanoTime >= 0L

        fun rescheduleOnShutdown() = synchronized(this) {
            if (state != DELAYED) return
            if (_delayed.value!!.remove(this)) {
                state = RESCHEDULED
                DefaultExecutor.schedule(this)
            } else
                state = REMOVED
        }

        final override fun dispose() = synchronized(this) {
                when (state) {
                    DELAYED -> _delayed.value?.remove(this)
                    RESCHEDULED -> DefaultExecutor.removeDelayedImpl(this)
                    else -> return
                }
                state = REMOVED
            }

        override fun toString(): String = "Delayed[nanos=$nanoTime]"
    }

    private inner class DelayedResumeTask(
        time: Long, timeUnit: TimeUnit,
        private val cont: CancellableContinuation<Unit>
    ) : DelayedTask(time, timeUnit) {
        override fun run() {
            with(cont) { resumeUndispatched(Unit) }
        }
    }

    private inner class DelayedRunnableTask(
        time: Long, timeUnit: TimeUnit,
        private val block: Runnable
    ) : DelayedTask(time, timeUnit) {
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