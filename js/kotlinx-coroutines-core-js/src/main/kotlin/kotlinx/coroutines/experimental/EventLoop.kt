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

import kotlinx.coroutines.experimental.internal.*
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Implemented by [CoroutineDispatcher] implementations that have event loop inside and can
 * be asked to process next event from their event queue.
 *
 * It may optionally implement [Delay] interface and support time-scheduled tasks. It is used by [runBlocking] to
 * continue processing events when invoked.
 */
public actual interface EventLoop {
    /**
     * Processes next event in this event loop.
     *
     * The result of this function is to be interpreted like this:
     * * `<= 0` -- there are potentially more events for immediate processing;
     * * `> 0` -- a number of milliseconds to wait for next scheduled event;
     * * [Double.MAX_VALUE] or infinity -- no more events.
     */
    public fun processNextEvent(): Double
}

private const val DELAYED = 0
private const val REMOVED = 1
private const val RESCHEDULED = 2

internal abstract class EventLoopBase: CoroutineDispatcher(), Delay, EventLoop {
    private val queue = LinkedListHead()
    private var delayed: Heap<DelayedTask>? = null

    protected abstract val isCompleted: Boolean

    private val nextTime: Double
        get() {
            if (!queue.isEmpty) return 0.0
            val nextDelayedTask = delayed?.peek() ?: return Double.MAX_VALUE
            return (nextDelayedTask.time - now()).coerceAtLeast(0.0)
        }

    override fun dispatch(context: CoroutineContext, block: Runnable) =
        enqueue(block.toQueuedTask())

    override fun scheduleResumeAfterDelay(time: Double, continuation: CancellableContinuation<Unit>) =
        schedule(DelayedResumeTask(time, continuation))

    override fun invokeOnTimeout(time: Double, block: Runnable): DisposableHandle =
        DelayedRunnableTask(time, block).also { schedule(it) }

    override fun processNextEvent(): Double {
        // queue all delayed tasks that are due to be executed
        val delayed = this.delayed
        if (delayed?.isEmpty == false) {
            val now = now()
            while (true) {
                delayed.removeFirstIf {
                    if (it.timeToExecute(now)) {
                        queue.addLast(it)
                        true // proceed with remove
                    } else
                        false
                } ?: break // quit loop when nothing more to remove
            }
        }
        // then process one event from queue
        (queue.removeFirstOrNull() as? QueuedTask)?.run()
        return nextTime
    }

    private fun Runnable.toQueuedTask(): QueuedTask =
        if (this is QueuedTask && isFresh) this else QueuedRunnableTask(this)

    private fun enqueue(queuedTask: QueuedTask) {
        if (!enqueueImpl(queuedTask))
            DefaultExecutor.enqueue(queuedTask)
    }

    private fun enqueueImpl(queuedTask: QueuedTask): Boolean {
        if (isCompleted) return false
        queue.addLast(queuedTask)
        return true
    }

    private fun schedule(delayedTask: DelayedTask) {
        if (!scheduleImpl(delayedTask)) {
            val remaining = delayedTask.time - now()
            DefaultExecutor.schedule(remaining, delayedTask)
        }
    }

    private fun scheduleImpl(delayedTask: DelayedTask): Boolean {
        if (isCompleted) return false
        val delayed = delayed ?: Heap<DelayedTask>().also { this.delayed = it }
        delayed.addLast(delayedTask)
        return true
    }

    protected fun rescheduleAllDelayed() {
        while (true) {
            val delayedTask = delayed?.removeFirstOrNull() ?: break
            delayedTask.rescheduleOnShutdown()
        }
    }

    internal abstract class QueuedTask : LinkedListNode(), Runnable

    private class QueuedRunnableTask(
        private val block: Runnable
    ) : QueuedTask() {
        override fun run() { block.run() }
        override fun toString(): String = block.toString()
    }

    internal abstract inner class DelayedTask(
        delay: Double
    ) : QueuedTask(), Comparable<DelayedTask>, DisposableHandle, HeapNode {
        override var index: Int = -1
        var state = DELAYED
        var handle = 0 // when state == RESCHEDULED
        val time: Double = now() + delay

        override fun compareTo(other: DelayedTask): Int {
            val dTime = time - other.time
            return when {
                dTime > 0 -> 1
                dTime < 0 -> -1
                else -> 0
            }
        }

        fun timeToExecute(now: Double): Boolean = now - time >= 0L

        fun rescheduleOnShutdown() {
            if (state != DELAYED) return
            if (delayed?.remove(this) == true) {
                state = RESCHEDULED
                handle = DefaultExecutor.schedule(time,this)
            } else
                state = REMOVED
        }

        final override fun dispose() {
            when (state) {
                DELAYED -> delayed?.remove(this)
                RESCHEDULED -> DefaultExecutor.removeScheduled(handle)
                else -> return
            }
            state = REMOVED
        }

        override fun toString(): String = "Delayed[nanos=$time]"
    }

    private inner class DelayedResumeTask(
        time: Double,
        private val cont: CancellableContinuation<Unit>
    ) : DelayedTask(time) {
        override fun run() {
            with(cont) { resumeUndispatched(Unit) }
        }
    }

    private inner class DelayedRunnableTask(
        time: Double,
        private val block: Runnable
    ) : DelayedTask(time) {
        override fun run() { block.run() }
        override fun toString(): String = super.toString() + block.toString()
    }
}

internal class BlockingEventLoop() : EventLoopBase() {
    public override var isCompleted: Boolean = false

    fun shutdown() {
        check(isCompleted) { "Shall be completed" }
        // complete processing of all queued tasks
        while (processNextEvent() <= 0) { /* spin */ }
        // reschedule the rest of delayed tasks
        rescheduleAllDelayed()
    }
}

private fun now(): Double = js("Date.now()") as Double