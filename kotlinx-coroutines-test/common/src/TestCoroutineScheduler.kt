/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlin.time.*

/**
 * This is a scheduler for coroutines used in tests, providing the delay-skipping behavior.
 *
 * [Test dispatchers][TestDispatcher] are parameterized with a scheduler. Several dispatchers can share the
 * same scheduler, in which case their knowledge about the virtual time will be synchronized. When the dispatchers
 * require scheduling an event at a later point in time, they notify the scheduler, which will establish the order of
 * the tasks.
 *
 * The scheduler can be queried to advance the time (via [advanceTimeBy]), run all the scheduled tasks advancing the
 * virtual time as needed (via [advanceUntilIdle]), or run the tasks that are scheduled to run as soon as possible but
 * haven't yet been dispatched (via [runCurrent]).
 */
@ExperimentalCoroutinesApi
public class TestCoroutineScheduler : AbstractCoroutineContextElement(TestCoroutineScheduler),
    CoroutineContext.Element {

    /** @suppress */
    public companion object Key : CoroutineContext.Key<TestCoroutineScheduler>

    /** This heap stores the knowledge about which dispatchers are interested in which moments of virtual time. */
    // TODO: all the synchronization is done via a separate lock, so a non-thread-safe priority queue can be used.
    private val events = ThreadSafeHeap<TestDispatchEvent<Any>>()

    /** Establishes that [currentTime] can't exceed the time of the earliest event in [events]. */
    private val lock = SynchronizedObject()

    /** This counter establishes some order on the events that happen at the same virtual time. */
    private val count = atomic(0L)

    /** The current virtual time in milliseconds. */
    @ExperimentalCoroutinesApi
    public var currentTime: Long = 0
        get() = synchronized(lock) { field }
        private set

    /** A channel for notifying about the fact that a dispatch recently happened. */
    private val dispatchEvents: Channel<Unit> = Channel(CONFLATED)

    /**
     * Registers a request for the scheduler to notify [dispatcher] at a virtual moment [timeDeltaMillis] milliseconds
     * later via [TestDispatcher.processEvent], which will be called with the provided [marker] object.
     *
     * Returns the handler which can be used to cancel the registration.
     */
    internal fun <T : Any> registerEvent(
        dispatcher: TestDispatcher,
        timeDeltaMillis: Long,
        marker: T,
        context: CoroutineContext,
        isCancelled: (T) -> Boolean
    ): DisposableHandle {
        require(timeDeltaMillis >= 0) { "Attempted scheduling an event earlier in time (with the time delta $timeDeltaMillis)" }
        checkSchedulerInContext(this, context)
        val count = count.getAndIncrement()
        val isForeground = context[BackgroundWork] === null
        return synchronized(lock) {
            val time = addClamping(currentTime, timeDeltaMillis)
            val event = TestDispatchEvent(dispatcher, count, time, marker as Any, isForeground) { isCancelled(marker) }
            events.addLast(event)
            /** can't be moved above: otherwise, [onDispatchEvent] could consume the token sent here before there's
             * actually anything in the event queue. */
            sendDispatchEvent(context)
            DisposableHandle {
                synchronized(lock) {
                    events.remove(event)
                }
            }
        }
    }

    /**
     * Runs the next enqueued task, advancing the virtual time to the time of its scheduled awakening,
     * unless [condition] holds.
     */
    internal fun tryRunNextTaskUnless(condition: () -> Boolean): Boolean {
        val event = synchronized(lock) {
            if (condition()) return false
            val event = events.removeFirstOrNull() ?: return false
            if (currentTime > event.time)
                currentTimeAheadOfEvents()
            currentTime = event.time
            event
        }
        event.dispatcher.processEvent(event.time, event.marker)
        return true
    }

    /**
     * Runs the enqueued tasks in the specified order, advancing the virtual time as needed until there are no more
     * tasks associated with the dispatchers linked to this scheduler.
     *
     * A breaking change from [TestCoroutineDispatcher.advanceTimeBy] is that it no longer returns the total number of
     * milliseconds by which the execution of this method has advanced the virtual time. If you want to recreate that
     * functionality, query [currentTime] before and after the execution to achieve the same result.
     */
    @ExperimentalCoroutinesApi
    public fun advanceUntilIdle(): Unit = advanceUntilIdleOr { events.none(TestDispatchEvent<*>::isForeground) }

    /**
     * [condition]: guaranteed to be invoked under the lock.
     */
    internal fun advanceUntilIdleOr(condition: () -> Boolean) {
        while (true) {
            if (!tryRunNextTaskUnless(condition))
                return
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
        require(delayTimeMillis >= 0) { "Can not advance time by a negative delay: $delayTimeMillis" }
        val startingTime = currentTime
        val targetTime = addClamping(startingTime, delayTimeMillis)
        while (true) {
            val event = synchronized(lock) {
                val timeMark = currentTime
                val event = events.removeFirstIf { targetTime > it.time }
                when {
                    event == null -> {
                        currentTime = targetTime
                        return
                    }
                    timeMark > event.time -> currentTimeAheadOfEvents()
                    else -> {
                        currentTime = event.time
                        event
                    }
                }
            }
            event.dispatcher.processEvent(event.time, event.marker)
        }
    }

    /**
     * Checks that the only tasks remaining in the scheduler are cancelled.
     */
    internal fun isIdle(strict: Boolean = true): Boolean =
        synchronized(lock) {
            if (strict) events.isEmpty else events.none { !it.isCancelled() }
        }

    /**
     * Notifies this scheduler about a dispatch event.
     *
     * [context] is the context in which the task will be dispatched.
     */
    internal fun sendDispatchEvent(context: CoroutineContext) {
        if (context[BackgroundWork] !== BackgroundWork)
            dispatchEvents.trySend(Unit)
    }

    /**
     * Consumes the knowledge that a dispatch event happened recently.
     */
    internal val onDispatchEvent: SelectClause1<Unit> get() = dispatchEvents.onReceive

    /**
     * Returns the [TimeSource] representation of the virtual time of this scheduler.
     */
    @ExperimentalCoroutinesApi
    @ExperimentalTime
    public val timeSource: TimeSource = object : AbstractLongTimeSource(DurationUnit.MILLISECONDS) {
        override fun read(): Long = currentTime
    }
}

// Some error-throwing functions for pretty stack traces
private fun currentTimeAheadOfEvents(): Nothing = invalidSchedulerState()

private fun invalidSchedulerState(): Nothing =
    throw IllegalStateException("The test scheduler entered an invalid state. Please report this at https://github.com/Kotlin/kotlinx.coroutines/issues.")

/** [ThreadSafeHeap] node representing a scheduled task, ordered by the planned execution time. */
private class TestDispatchEvent<T>(
    @JvmField val dispatcher: TestDispatcher,
    private val count: Long,
    @JvmField val time: Long,
    @JvmField val marker: T,
    @JvmField val isForeground: Boolean,
    // TODO: remove once the deprecated API is gone
    @JvmField val isCancelled: () -> Boolean
) : Comparable<TestDispatchEvent<*>>, ThreadSafeHeapNode {
    override var heap: ThreadSafeHeap<*>? = null
    override var index: Int = 0

    override fun compareTo(other: TestDispatchEvent<*>) =
        compareValuesBy(this, other, TestDispatchEvent<*>::time, TestDispatchEvent<*>::count)

    override fun toString() = "TestDispatchEvent(time=$time, dispatcher=$dispatcher${if (isForeground) "" else ", background"})"
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

/**
 * A coroutine context key denoting that the work is to be executed in the background.
 * @see [TestScope.backgroundScope]
 */
internal object BackgroundWork : CoroutineContext.Key<BackgroundWork>, CoroutineContext.Element {
    override val key: CoroutineContext.Key<*>
        get() = this

    override fun toString(): String = "BackgroundWork"
}

private fun<T> ThreadSafeHeap<T>.none(predicate: (T) -> Boolean) where T: ThreadSafeHeapNode, T: Comparable<T> =
    find(predicate) == null
