/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.*

/**
 * Control the virtual clock time of a [CoroutineDispatcher].
 *
 * Testing libraries may expose this interface to tests instead of [TestCoroutineDispatcher].
 */
@ExperimentalCoroutinesApi
interface DelayController {
    /**
     * Returns the current virtual clock-time as it is known to this Dispatcher.
     *
     * @return The virtual clock-time
     */
    @ExperimentalCoroutinesApi
    fun currentTime(): Long

    /**
     * Moves the Dispatcher's virtual clock forward by a specified amount of time.
     *
     * The amount the clock is progressed may be larger than the requested delayTimeMillis if the code under test uses
     * blocking coroutines.
     *
     * @param delayTimeMillis The amount of time to move the CoroutineContext's clock forward.
     * @return The amount of delay-time that this Dispatcher's clock has been forwarded.
     */
    @ExperimentalCoroutinesApi
    fun advanceTimeBy(delayTimeMillis: Long): Long


    /**
     * Immediately execute all pending tasks and advance the virtual clock-time to the last delay.
     *
     * @return the amount of delay-time that this Dispatcher's clock has been forwarded in milliseconds.
     */
    @ExperimentalCoroutinesApi
    fun advanceUntilIdle(): Long

    /**
     * Run any tasks that are pending at or before the current virtual clock-time.
     *
     * Calling this function will never advance the clock.
     */
    @ExperimentalCoroutinesApi
    fun runCurrent()

    /**
     * Test code must call this after test code completes to ensure that the dispatcher is properly cleaned up.
     *
     * @throws UncompletedCoroutinesError if any pending tasks are active, however it will not throw for suspended
     * coroutines.
     */
    @ExperimentalCoroutinesApi
    @Throws(UncompletedCoroutinesError::class)
    fun cleanupTestCoroutines()

    /**
     * Run a block of code in a paused dispatcher.
     *
     * By pausing the dispatcher any new coroutines will not execute immediately. After block executes, the dispatcher
     * will resume auto-advancing.
     *
     * This is useful when testing functions that start a coroutine. By pausing the dispatcher assertions or
     * setup may be done between the time the coroutine is created and started.
     */
    @ExperimentalCoroutinesApi
    suspend fun pauseDispatcher(block: suspend () -> Unit)

    /**
     * Pause the dispatcher.
     *
     * When paused, the dispatcher will not execute any coroutines automatically, and you must call [runCurrent] or
     * [advanceTimeBy], or [advanceUntilIdle] to execute coroutines.
     */
    @ExperimentalCoroutinesApi
    fun pauseDispatcher()

    /**
     * Resume the dispatcher from a paused state.
     *
     * Resumed dispatchers will automatically progress through all coroutines scheduled at the current time. To advance
     * time and execute coroutines scheduled in the future use, one of [advanceTimeBy],
     * or [advanceUntilIdle].
     */
    @ExperimentalCoroutinesApi
    fun resumeDispatcher()
}

/**
 * Thrown when a test has completed and there are tasks that are not completed or cancelled.
 */
@ExperimentalCoroutinesApi
class UncompletedCoroutinesError(message: String, cause: Throwable? = null): AssertionError(message, cause)

/**
 * [CoroutineDispatcher] that can be used in tests for both immediate and lazy execution of coroutines.
 *
 * By default, [TestCoroutineDispatcher] will be immediate. That means any tasks scheduled to be run without delay will
 * be immediately executed. If they were scheduled with a delay, the virtual clock-time must be advanced via one of the
 * methods on [DelayController]
 *
 * When swiched to lazy execution any coroutines started via [launch] or [async] will
 * not execute until a call to [DelayController.runCurrent] or the virtual clock-time has been advanced via one of the
 * methods on [DelayController].
 *
 * @see DelayController
 */
@ExperimentalCoroutinesApi
class TestCoroutineDispatcher:
        CoroutineDispatcher(),
        Delay,
        DelayController {

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
    private var counter = AtomicLong(0)

    // Storing time in nanoseconds internally.
    private var time = AtomicLong(0)

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        if (dispatchImmediately) {
            block.run()
        } else {
            post(block)
        }
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        postDelayed(CancellableContinuationRunnable(continuation) { resumeUndispatched(Unit) }, timeMillis)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        val node = postDelayed(block, timeMillis)
        return object : DisposableHandle {
            override fun dispose() {
                queue.remove(node)
            }
        }
    }

    override fun toString(): String {
        return "TestCoroutineDispatcher[currentTime=${time}ms, queued=${queue.size}]"
    }

    private fun post(block: Runnable) =
            queue.addLast(TimedRunnable(block, counter.getAndIncrement()))

    private fun postDelayed(block: Runnable, delayTime: Long) =
            TimedRunnable(block, counter.getAndIncrement(), time.get() + delayTime)
                    .also {
                        queue.addLast(it)
                    }


    private fun doActionsUntil(targetTime: Long) {
        while (true) {
            val current = queue.removeFirstIf { it.time <= targetTime } ?: break
            // If the scheduled time is 0 (immediate) use current virtual time
            time.getAndAccumulate(current.time) { currentValue: Long, proposedValue: Long ->
                if (proposedValue != 0L) {
                    proposedValue
                } else {
                    currentValue
                }
            }
            current.run()
        }
    }

    override fun currentTime() = time.get()

    override fun advanceTimeBy(delayTimeMillis: Long): Long {
        val oldTime = time.get()
        advanceUntilTime(oldTime + delayTimeMillis)
        return time.get() - oldTime
    }

    /**
     * Moves the CoroutineContext's clock-time to a particular moment in time.
     *
     * @param targetTime The point in time to which to move the CoroutineContext's clock (milliseconds).
     */
    private fun advanceUntilTime(targetTime: Long) {
        doActionsUntil(targetTime)
        time.getAndAccumulate(targetTime) { currentValue: Long, proposedValue: Long ->
            if (currentValue < proposedValue) {
                proposedValue
            } else {
                currentValue
            }
        }
        if (targetTime > time.get()) time
    }

    override fun advanceUntilIdle(): Long {
        val oldTime = time.get()
        while(!queue.isEmpty) {
            runCurrent()
            val next = queue.peek() ?: break
            advanceUntilTime(next.time)
        }
        return time.get() - oldTime
    }

    override fun runCurrent() = doActionsUntil(time.get())

    override suspend fun pauseDispatcher(block: suspend () -> Unit) {
        val previous = dispatchImmediately
        dispatchImmediately = false
        try {
            block()
        } finally {
            dispatchImmediately = previous
        }
    }

    override fun pauseDispatcher() {
        dispatchImmediately = false
    }

    override fun resumeDispatcher() {
        dispatchImmediately = true
    }

    override fun cleanupTestCoroutines() {
        // process any pending cancellations or completions, but don't advance time
        doActionsUntil(time.get())

        // run through all pending tasks, ignore any submitted coroutines that are not active
        val pendingTasks = mutableListOf<TimedRunnable>()
        while (true) {
            pendingTasks += queue.removeFirstOrNull() ?: break
        }
        val activeDelays = pendingTasks.map { it.runnable as? CancellableContinuationRunnable<*> }
                .filterNotNull()
                .filter { it.continuation.isActive }

        val activeTimeouts = pendingTasks.filter { it.runnable !is CancellableContinuationRunnable<*> }
        if (activeDelays.isNotEmpty() || activeTimeouts.isNotEmpty()) {
            throw UncompletedCoroutinesError("Unfinished coroutines during teardown. Ensure all coroutines are" +
                    " completed or cancelled by your test.")
        }
    }
}


/**
 * This class exists to allow cleanup code to avoid throwing for cancelled continuations scheduled
 * in the future.
 */
private class CancellableContinuationRunnable<T>(
        val continuation: CancellableContinuation<T>,
        private val block: CancellableContinuation<T>.() -> Unit) : Runnable {
    override fun run() = continuation.block()
}

/**
 * A Runnable for our event loop that represents a task to perform at a time.
 */
private class TimedRunnable(
        val runnable: Runnable,
        private val count: Long = 0,
        @JvmField internal val time: Long = 0
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