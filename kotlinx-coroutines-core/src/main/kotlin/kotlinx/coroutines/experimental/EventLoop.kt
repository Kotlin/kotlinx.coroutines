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

import kotlinx.coroutines.experimental.internal.LockFreeLinkedListHead
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListNode
import java.util.concurrent.ConcurrentSkipListMap
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.locks.LockSupport
import kotlin.coroutines.experimental.CoroutineContext

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

    public companion object Factory {
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
        public operator fun invoke(thread: Thread = Thread.currentThread(), parentJob: Job? = null): CoroutineDispatcher =
            EventLoopImpl(thread).apply {
                if (parentJob != null) initParentJob(parentJob)
            }
    }
}

internal class EventLoopImpl(
    private val thread: Thread
) : CoroutineDispatcher(), EventLoop, Delay {
    private val queue = LockFreeLinkedListHead()
    private val delayed = ConcurrentSkipListMap<DelayedTask, DelayedTask>()
    private val nextSequence = AtomicLong()
    private var parentJob: Job? = null

    fun initParentJob(coroutine: Job) {
        require(this.parentJob == null)
        this.parentJob = coroutine
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        if (scheduleQueued(QueuedRunnableTask(block))) {
            unpark()
        } else {
            block.run()
        }
    }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        if (scheduleDelayed(DelayedResumeTask(time, unit, continuation))) {
            // todo: we should unpark only when this delayed task became first in the queue
            unpark()
        } else {
            scheduledExecutor.schedule(ResumeRunnable(continuation), time, unit)
        }
    }

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle =
        DelayedRunnableTask(time, unit, block).also { scheduleDelayed(it) }

    override fun processNextEvent(): Long {
        if (Thread.currentThread() !== thread) return Long.MAX_VALUE
        // queue all delayed tasks that are due to be executed
        while (true) {
            val delayedTask = delayed.firstEntry()?.key ?: break
            val now = System.nanoTime()
            if (delayedTask.nanoTime - now > 0) break
            if (!scheduleQueued(delayedTask)) break
            delayed.remove(delayedTask)
        }
        // then process one event from queue
        (queue.removeFirstOrNull() as? QueuedTask)?.let { queuedTask ->
            queuedTask()
        }
        if (!queue.isEmpty) return 0
        val nextDelayedTask = delayed.firstEntry()?.key ?: return Long.MAX_VALUE
        return nextDelayedTask.nanoTime - System.nanoTime()
    }

    fun shutdown() {
        // complete processing of all queued tasks
        while (true) {
            val queuedTask = (queue.removeFirstOrNull() ?: break) as QueuedTask
            queuedTask()
        }
        // cancel all delayed tasks
        while (true) {
            val delayedTask = delayed.pollFirstEntry()?.key ?: break
            delayedTask.cancel()
        }
    }

    private fun scheduleQueued(queuedTask: QueuedTask): Boolean {
        if (parentJob == null) {
            queue.addLast(queuedTask)
            return true
        }
        return queue.addLastIf(queuedTask, { !parentJob!!.isCompleted })
    }

    private fun scheduleDelayed(delayedTask: DelayedTask): Boolean {
        delayed.put(delayedTask, delayedTask)
        if (parentJob?.isActive != false) return true
        delayedTask.dispose()
        return false
    }

    private fun unpark() {
        if (Thread.currentThread() !== thread)
            LockSupport.unpark(thread)
    }

    private abstract class QueuedTask : LockFreeLinkedListNode(), () -> Unit

    private class QueuedRunnableTask(
        private val block: Runnable
    ) : QueuedTask() {
        override fun invoke() { block.run() }
    }

    private abstract inner class DelayedTask(
        time: Long, timeUnit: TimeUnit
    ) : QueuedTask(), Comparable<DelayedTask>, DisposableHandle {
        @JvmField val nanoTime: Long = System.nanoTime() + timeUnit.toNanos(time)
        @JvmField val sequence: Long = nextSequence.getAndIncrement()

        override fun compareTo(other: DelayedTask): Int {
            val dTime = nanoTime - other.nanoTime
            if (dTime > 0) return 1
            if (dTime < 0) return -1
            val dSequence = sequence - other.sequence
            return if (dSequence > 0) 1 else if (dSequence < 0) -1 else 0
        }

        override final fun dispose() {
            delayed.remove(this)
            cancel()
        }

        open fun cancel() {}
    }

    private inner class DelayedResumeTask(
        time: Long, timeUnit: TimeUnit,
        private val cont: CancellableContinuation<Unit>
    ) : DelayedTask(time, timeUnit) {
        override fun invoke() {
            with(cont) { resumeUndispatched(Unit) }
        }
        override fun cancel() {
            if (!cont.isActive) return
            val remaining = nanoTime - System.nanoTime()
            scheduledExecutor.schedule(ResumeRunnable(cont), remaining, TimeUnit.NANOSECONDS)
        }
    }

    private inner class DelayedRunnableTask(
        time: Long, timeUnit: TimeUnit,
        private val block: Runnable
    ) : DelayedTask(time, timeUnit) {
        override fun invoke() { block.run() }
    }
}
