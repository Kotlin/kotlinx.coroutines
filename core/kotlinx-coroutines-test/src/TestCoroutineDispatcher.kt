package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.ThreadSafeHeap
import kotlinx.coroutines.test.internal.ThreadSafeHeapNode
import java.util.concurrent.TimeUnit
import kotlin.coroutines.CoroutineContext

/**
 * Control the virtual clock time of a [CoroutineDispatcher].
 *
 * Testing libraries may expose this interface to tests instead of [TestCoroutineDispatcher].
 */
interface DelayController {
    /**
     * Returns the current virtual clock-time as it is known to this Dispatcher.
     *
     * @param unit The [TimeUnit] in which the clock-time must be returned.
     * @return The virtual clock-time
     */
    fun currentTime(unit: TimeUnit = TimeUnit.MILLISECONDS): Long

    /**
     * Moves the Dispatcher's virtual clock forward by a specified amount of time.
     *
     * The amount the clock is progressed may be larger than the requested delayTime if the code under test uses
     * blocking coroutines.
     *
     * @param delayTime The amount of time to move the CoroutineContext's clock forward.
     * @param unit The [TimeUnit] in which [delayTime] and the return value is expressed.
     * @return The amount of delay-time that this Dispatcher's clock has been forwarded.
     */
    fun advanceTimeBy(delayTime: Long, unit: TimeUnit = TimeUnit.MILLISECONDS): Long

    /**
     * Moves the current virtual clock forward just far enough so the next delay will return.
     *
     * @return the amount of delay-time that this Dispatcher's clock has been forwarded.
     */
    fun advanceTimeToNextDelayed(): Long

    /**
     * Immediately execute all pending tasks and advance the virtual clock-time to the last delay.
     *
     * @return the amount of delay-time that this Dispatcher's clock has been forwarded.
     */
    fun advanceUntilIdle(): Long

    /**
     * Run any tasks that are pending at or before the current virtual clock-time.
     *
     * Calling this function will never advance the clock.
     */
    fun runCurrent()

    /**
     * Call after a test case completes.
     *
     * @throws UncompletedCoroutinesError if any pending tasks are active, however it will not throw for suspended
     * coroutines that called await.
     */
    @Throws(UncompletedCoroutinesError::class)
    fun cleanupTestCoroutines()

    /**
     * When true, this dispatcher will perform as an immediate executor.
     *
     * It will immediately run any tasks, which means it will auto-advance the virtual clock-time to the last pending
     * delay.
     *
     * Test code will rarely call this method directly., Instead use a test builder like [asyncTest], [runBlockingTest] or
     * the convenience methods [TestCoroutineDispatcher.runBlocking] and [TestCoroutineScope.runBlocking].
     *
     * ```
     * @Test
     * fun aTest() {
     *     val scope = TestCoroutineScope() // dispatchImmediately is false
     *     scope.async {
     *         // delay will be pending execution (lazy mode)
     *         delay(1_000)
     *     }
     *
     *     scope.runBlocking {
     *         // the pending delay will immediately execute
     *         // dispatchImmediately is true
     *     }
     *
     *     // scope is returned to lazy mode
     *     // dispatchImmediately is false
     * }
     * ```
     *
     * Setting this to true will immediately execute any pending tasks and advance the virtual clock-time to the last
     * pending delay. While true, dispatch will continue to execute immediately, auto-advancing the virtual clock-time.
     *
     * Setting it to false will resume lazy execution.
     */
    var dispatchImmediately: Boolean
}

/**
 * Thrown when a test has completed by there are tasks that are not completed or cancelled.
 */
class UncompletedCoroutinesError(message: String, cause: Throwable? = null): AssertionError(message, cause)

/**
 * [CoroutineDispatcher] that can be used in tests for both immediate  and lazy execution of coroutines.
 *
 * By default, [TestCoroutineDispatcher] will be lazy. That means any coroutines started via [launch] or [async] will
 * not execute until a call to [DelayController.runCurrent] or the virtual clock-time has been advanced via one of the
 * methods on [DelayController].
 *
 * When switched to immediate mode, any tasks will be immediately executed. If they were scheduled with a delay,
 * the virtual clock-time will auto-advance to the last submitted delay.
 *
 * @see DelayController
 */
class TestCoroutineDispatcher:
        CoroutineDispatcher(),
        Delay,
        DelayController {

    override var dispatchImmediately = false
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
    private var counter = 0L

    // Storing time in nanoseconds internally.
    private var time = 0L

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        if (dispatchImmediately) {
            block.run()
        } else {
            post(block)
        }
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        postDelayed(CancellableContinuationRunnable(continuation) { resumeUndispatched(Unit) }, timeMillis)
        if (dispatchImmediately) {
//            advanceTimeBy(timeMillis, TimeUnit.MILLISECONDS)
        }
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        val node = postDelayed(block, timeMillis)
        return object : DisposableHandle {
            override fun dispose() {
                queue.remove(node)
            }
        }
    }

//    override fun processNextEvent(): Long {
//        val current = queue.peek()
//        if (current != null) {
//            // Automatically advance time for EventLoop callbacks
//            triggerActions(current.time)
//        }
//        return if (queue.isEmpty) Long.MAX_VALUE else 0L
//    }

    override fun toString(): String = "TestCoroutineDispatcher[time=$time ns]"

    private fun post(block: Runnable) =
            queue.addLast(TimedRunnable(block, counter++))

    private fun postDelayed(block: Runnable, delayTime: Long) =
            TimedRunnable(block, counter++, time + TimeUnit.MILLISECONDS.toNanos(delayTime))
                    .also {
                        queue.addLast(it)
                    }


    private fun triggerActions(targetTime: Long) {
        while (true) {
            val current = queue.removeFirstIf { it.time <= targetTime } ?: break
            // If the scheduled time is 0 (immediate) use current virtual time
            if (current.time != 0L) time = current.time
            current.run()
        }
    }

    override fun currentTime(unit: TimeUnit)=
            unit.convert(time, TimeUnit.NANOSECONDS)

    override fun advanceTimeBy(delayTime: Long, unit: TimeUnit): Long {
        val oldTime = time
        advanceTimeTo(oldTime + unit.toNanos(delayTime), TimeUnit.NANOSECONDS)
        return unit.convert(time - oldTime, TimeUnit.NANOSECONDS)
    }

    /**
     * Moves the CoroutineContext's clock-time to a particular moment in time.
     *
     * @param targetTime The point in time to which to move the CoroutineContext's clock.
     * @param unit The [TimeUnit] in which [targetTime] is expressed.
     */
    private fun advanceTimeTo(targetTime: Long, unit: TimeUnit) {
        val nanoTime = unit.toNanos(targetTime)
        triggerActions(nanoTime)
        if (nanoTime > time) time = nanoTime
    }

    override fun advanceTimeToNextDelayed(): Long {
        val oldTime = time
        runCurrent()
        val next = queue.peek() ?: return 0
        advanceTimeTo(next.time, TimeUnit.NANOSECONDS)
        return time - oldTime
    }

    override fun advanceUntilIdle(): Long {
        val oldTime = time
        while(!queue.isEmpty) {
            advanceTimeToNextDelayed()
        }
        return time - oldTime
    }

    override fun cleanupTestCoroutines() {
        // process any pending cancellations or completions, but don't advance time
        triggerActions(time)

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

    override fun runCurrent() = triggerActions(time)
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