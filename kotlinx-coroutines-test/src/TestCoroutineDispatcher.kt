/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.update
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.ConflatedBroadcastChannel
import kotlinx.coroutines.internal.ThreadSafeHeap
import kotlinx.coroutines.internal.ThreadSafeHeapNode
import kotlinx.coroutines.test.DelayController.QueueState.*
import kotlin.coroutines.CoroutineContext
import kotlin.math.max

/**
 * [CoroutineDispatcher] that performs both immediate and lazy execution of coroutines in tests
 * and implements [DelayController] to control its virtual clock.
 *
 * By default, [TestCoroutineDispatcher] is immediate. That means any tasks scheduled to be run without delay are
 * immediately executed. If they were scheduled with a delay, the virtual clock-time must be advanced via one of the
 * methods on [DelayController].
 *
 * When switched to lazy execution using [pauseDispatcher] any coroutines started via [launch] or [async] will
 * not execute until a call to [DelayController.runCurrent] or the virtual clock-time has been advanced via one of the
 * methods on [DelayController].
 *
 * @see DelayController
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public class TestCoroutineDispatcher: CoroutineDispatcher(), Delay, DelayController {
    private var dispatchImmediately = true
        set(value) {
            field = value
            if (value) {
                // there may already be tasks from setup code we need to run
                advanceUntilIdle()
            }
        }

    // The ordered queue for the runnable tasks.
    private val queue = ThreadSafeHeap<TimedRunnable>()

    // The per-scheduler global order counter.
    private val _counter = atomic(0L)

    // Storing time in nanoseconds internally.
    private val _time = atomic(0L)

    override val queueState = ConflatedBroadcastChannel<DelayController.QueueState>(Idle)
        
    /** @suppress */
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        if (dispatchImmediately) {
            block.run()
        } else {
            post(block)
        }
    }

    /** @suppress */
    @InternalCoroutinesApi
    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        post(block)
    }

    /** @suppress */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        postDelayed(CancellableContinuationRunnable(continuation) { resumeUndispatched(Unit) }, timeMillis)
    }

    /** @suppress */
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        val node = postDelayed(block, timeMillis)
        return object : DisposableHandle {
            override fun dispose() {
                queue.remove(node)
                updateQueueObservers()
            }
        }
    }

    /** @suppress */
    override fun toString(): String {
        return "TestCoroutineDispatcher[currentTime=${currentTime}ms, queued=${queue.size}]"
    }

    private fun post(block: Runnable) {
        queue.addLast(TimedRunnable(block, _counter.getAndIncrement()))
        updateQueueObservers()
    }

    private fun postDelayed(block: Runnable, delayTime: Long): TimedRunnable {
        return TimedRunnable(block, _counter.getAndIncrement(), safePlus(currentTime, delayTime))
                .also {
                    queue.addLast(it)
                    updateQueueObservers()
                }
    }

    private fun safePlus(currentTime: Long, delayTime: Long): Long {
        check(delayTime >= 0)
        val result = currentTime + delayTime
        if (result < currentTime) return Long.MAX_VALUE // clam on overflow
        return result
    }

    private fun doActionsUntil(targetTime: Long) {
        while (true) {
            val current = queue.removeFirstIf { it.time <= targetTime } ?: break
            // If the scheduled time is 0 (immediate) use current virtual time
            if (current.time != 0L) _time.value = current.time
            current.run()
        }
    }

    /** @suppress */
    override val currentTime get() = _time.value

    /** @suppress */
    override fun advanceTimeBy(delayTimeMillis: Long): Long {
        val oldTime = currentTime
        advanceUntilTime(oldTime + delayTimeMillis)
        updateQueueObservers()
        return currentTime - oldTime
    }

    /**
     * Moves the CoroutineContext's clock-time to a particular moment in time.
     *
     * @param targetTime The point in time to which to move the CoroutineContext's clock (milliseconds).
     */
    private fun advanceUntilTime(targetTime: Long) {
        doActionsUntil(targetTime)
        _time.update { currentValue -> max(currentValue, targetTime) }
        updateQueueObservers()
    }

    /** @suppress */
    override fun advanceUntilIdle(): Long {
        val oldTime = currentTime
        while(!queue.isEmpty) {
            runCurrent()
            val next = queue.peek() ?: break
            advanceUntilTime(next.time)
        }

        updateQueueObservers()
        return currentTime - oldTime
    }

    /** @suppress */
    override fun runCurrent() {
        doActionsUntil(currentTime)
        updateQueueObservers()
    }

    /** @suppress */
    override suspend fun pauseDispatcher(block: suspend () -> Unit) {
        val previous = dispatchImmediately
        dispatchImmediately = false
        try {
            block()
        } finally {
            dispatchImmediately = previous
        }
    }

    /** @suppress */
    override fun pauseDispatcher() {
        dispatchImmediately = false
    }

    /** @suppress */
    override fun resumeDispatcher() {
        dispatchImmediately = true
    }

    /** @suppress */
    override fun cleanupTestCoroutines() {
        // process any pending cancellations or completions, but don't advance time
        doActionsUntil(currentTime)
        updateQueueObservers()

        // run through all pending tasks, ignore any submitted coroutines that are not active
        val pendingTasks = mutableListOf<TimedRunnable>()
        while (true) {
            pendingTasks += queue.removeFirstOrNull() ?: break
        }
        val activeDelays = pendingTasks
            .mapNotNull { it.runnable as? CancellableContinuationRunnable<*> }
            .filter { it.continuation.isActive }

        val activeTimeouts = pendingTasks.filter { it.runnable !is CancellableContinuationRunnable<*> }
        if (activeDelays.isNotEmpty() || activeTimeouts.isNotEmpty()) {
            throw UncompletedCoroutinesError(
                "Unfinished coroutines during teardown. Ensure all coroutines are" +
                    " completed or cancelled by your test."
            )
        }
    }

    private fun updateQueueObservers() {
        // note: this will be called from any thread, and is safe lock-free in runBlockingTest but to guard against
        // third party code code updating this will use a lock
        synchronized(queue) {
            val next = queue.peek()
            when {
                next == null-> queueState.offerIfChanged(Idle)
                next.time <= currentTime -> queueState.offerIfChanged(HasCurrentTask)
                next.time > currentTime -> queueState.offerIfChanged(HasDelayedTask)
            }
        }
    }

    private fun ConflatedBroadcastChannel<DelayController.QueueState>.offerIfChanged(element: DelayController.QueueState) {
        if (valueOrNull != element) {
            offer(element)
        }
    }
}

/**
 * This class exists to allow cleanup code to avoid throwing for cancelled continuations scheduled
 * in the future.
 */
private class CancellableContinuationRunnable<T>(
    @JvmField val continuation: CancellableContinuation<T>,
    private val block: CancellableContinuation<T>.() -> Unit
) : Runnable {
    override fun run() = continuation.block()
}

/**
 * A Runnable for our event loop that represents a task to perform at a time.
 */
private class TimedRunnable(
    @JvmField val runnable: Runnable,
    private val count: Long = 0,
    @JvmField val time: Long = 0
) : Comparable<TimedRunnable>, Runnable by runnable, ThreadSafeHeapNode {
    override var heap: ThreadSafeHeap<*>? = null
    override var index: Int = 0

    override fun compareTo(other: TimedRunnable) = if (time == other.time) {
        count.compareTo(other.count)
    } else {
        time.compareTo(other.time)
    }

    override fun toString() = "TimedRunnable(time=$time, run=$runnable)"
}