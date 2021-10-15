/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * This is a scheduler for coroutines used in tests, providing the delay-skipping behavior.
 *
 * [Test dispatchers][TestCoroutineDispatcher] are parameterized with a scheduler. Several dispatchers can share the
 * same scheduler, in which case * their knowledge about the virtual time will be synchronized. When the dispatchers
 * require scheduling an event at a * later point in time, they notify the scheduler, which will establish the order of
 * the tasks.
 *
 * The scheduler can be queried to advance the time (via [advanceTimeBy]), run all the scheduled tasks advancing the
 * virtual time as needed (via [advanceUntilIdle]), or run the tasks that are scheduled to run as soon as possible but
 * haven't yet been dispatched (via [runCurrent]).
 */
@ExperimentalCoroutinesApi
// TODO: maybe make this a `TimeSource`?
public class TestCoroutineScheduler: AbstractCoroutineContextElement(TestCoroutineScheduler), CoroutineContext.Element {

    public companion object Key: CoroutineContext.Key<TestCoroutineScheduler>

    /** This heap stores the knowledge about which dispatchers are interested in which moments of virtual time. */
    // TODO: all the synchronization is done via a separate lock, so a non-thread-safe priority queue can be used.
    private val events = ThreadSafeHeap<TestDispatchEvent<Any>>()

    /** Establishes that [currentTime] can't exceed the time of the earliest event in [events]. */
    private val lock = SynchronizedObject()

    /** This counter establishes some order on the events that happen at the same virtual time. */
    private val count = atomic(0L)

    /** The current virtual time. */
    @ExperimentalCoroutinesApi
    public var currentTime: Long = 0
        get() = synchronized(lock) { field }
        private set

    /**
     * Registers a request for the scheduler to notify [dispatcher] at a virtual moment [timeDeltaMillis] milliseconds later
     * via [TestDispatcher.processEvent], which will be called with the provided [marker] object.
     *
     * Returns the handler which can be used to cancel the registration.
     */
    internal fun <T : Any> registerEvent(
        dispatcher: TestDispatcher,
        timeDeltaMillis: Long,
        marker: T,
        isCancelled : (T) -> Boolean
    ): DisposableHandle {
        require(timeDeltaMillis >= 0) { "Attempted scheduling an event earlier in time (with the time delta $timeDeltaMillis)" }
        val count = count.getAndIncrement()
        return synchronized(lock) {
            val time = addClamping(currentTime, timeDeltaMillis)
            val event = TestDispatchEvent(dispatcher, count, time, marker as Any) { isCancelled(marker) }
            events.addLast(event)
            DisposableHandle {
                synchronized(lock) {
                    events.remove(event)
                }
            }
        }
    }

    /**
     * Runs the enqueued tasks in the specified order, advancing the virtual time as needed until there are no more
     * tasks associated with the dispatchers linked to this scheduler.
     *
     * A breaking change from [TestCoroutineDispatcher.advanceTimeBy] is that it no longer returns the total amount of
     * milliseconds by which the execution of this method has advanced the virtual time. If you want to recreate that
     * functionality, query [currentTime] before and after the execution to achieve the same result.
     */
    @ExperimentalCoroutinesApi
    public fun advanceUntilIdle() {
        while (!events.isEmpty) {
            val event = synchronized(lock) {
                val event = events.removeFirstOrNull() ?: return
                if (currentTime > event.time)
                    currentTimeAheadOfEvents()
                currentTime = event.time
                event
            }
            event.dispatcher.processEvent(event.time, event.marker)
        }
    }

    /**
     * Runs the tasks that are scheduled to execute at this moment of virtual time.
     */
    @ExperimentalCoroutinesApi
    public fun runCurrent() {
        val timeMark = synchronized(lock) { currentTime }
        while (true) {
            val event = synchronized(lock) {
                events.removeFirstIf { it.time <= timeMark } ?: return
            }
            event.dispatcher.processEvent(event.time, event.marker)
        }
    }

    /**
     * Moves the virtual clock of this dispatcher forward by [the specified amount][delayTimeMillis], running the
     * scheduled tasks in the meantime.
     *
     * Breaking changes from [TestCoroutineDispatcher.advanceTimeBy]:
     * * Intentionally doesn't return a `Long` value, as its use cases are unclear. We may restore it in the future;
     *   please describe your use cases at [the issue tracker](https://github.com/Kotlin/kotlinx.coroutines/issues/).
     *   For now, it's possible to query [currentTime] before and after execution of this method, to the same effect.
     * * It doesn't run the tasks that are scheduled at exactly [currentTime] + [delayTimeMillis]. For example,
     *   advancing the time by one millisecond used to run the tasks at the current millisecond *and* the next
     *   millisecond, but now will stop just before executing any task starting at the next millisecond.
     * * Overflowing the target time used to lead to nothing being done, but will now run the tasks scheduled at up to
     *   (but not including) [Long.MAX_VALUE].
     *
     * @throws IllegalStateException if passed a negative [delay][delayTimeMillis].
     */
    @ExperimentalCoroutinesApi
    public fun advanceTimeBy(delayTimeMillis: Long) {
        require(delayTimeMillis >= 0) { "" }
        val startingTime = currentTime
        val targetTime = addClamping(startingTime, delayTimeMillis)
        while (true) {
            val event = synchronized(lock) {
                val timeMark = currentTime
                val event = events.peek()
                when {
                    event == null || targetTime <= event.time -> {
                        currentTime = targetTime
                        return
                    }
                    timeMark > event.time -> currentTimeAheadOfEvents()
                    else -> {
                        val event2 = events.removeFirstOrNull()
                        if (event !== event2) concurrentModificationUnderLock()
                        currentTime = event.time
                        event2
                    }
                }
            }
            event.dispatcher.processEvent(event.time, event.marker)
        }
    }

    /**
     * Checks that the only tasks remaining in the scheduler are cancelled.
     */
    // TODO: also completely empties the queue, as there's no nondestructive way to iterate over [ThreadSafeHeap]
    internal fun isIdle(): Boolean {
        synchronized(lock) {
            val presentEvents = mutableListOf<TestDispatchEvent<*>>()
            while (true) {
                presentEvents += events.removeFirstOrNull() ?: break
            }
            return presentEvents.all { it.isCancelled() }
        }
    }
}

// Some error-throwing functions for pretty stack traces
private fun currentTimeAheadOfEvents(): Nothing = invalidSchedulerState()
private fun concurrentModificationUnderLock(): Nothing = invalidSchedulerState()

private fun invalidSchedulerState(): Nothing =
    throw IllegalStateException("The test scheduler entered an invalid state. Please report this at https://github.com/Kotlin/kotlinx.coroutines/issues.")

/** [ThreadSafeHeap] node representing a scheduled task, ordered by the planned execution time. */
private class TestDispatchEvent<T>(
    @JvmField val dispatcher: TestDispatcher,
    private val count: Long,
    @JvmField val time: Long,
    @JvmField val marker: T,
    val isCancelled: () -> Boolean
) : Comparable<TestDispatchEvent<*>>, ThreadSafeHeapNode {
    override var heap: ThreadSafeHeap<*>? = null
    override var index: Int = 0

    override fun compareTo(other: TestDispatchEvent<*>) = if (time == other.time) {
        count.compareTo(other.count)
    } else {
        time.compareTo(other.time)
    }

    override fun toString() = "TestDispatchEvent(time=$time, dispatcher=$dispatcher)"
}

// works with positive `a`, `b`
private fun addClamping(a: Long, b: Long): Long = (a + b).let { if (it >= 0) it else Long.MAX_VALUE }

internal fun checkSchedulerInContext(scheduler: TestCoroutineScheduler, context: CoroutineContext) {
    context[TestCoroutineScheduler]?.let {
        check(it === scheduler) {
            "Detected use of different schedulers. If you need to use several test coroutine dispatchers, " +
                "create one `TestCoroutineScheduler` and pass it to each of them."
        }
    }
}
