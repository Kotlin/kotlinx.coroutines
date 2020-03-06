/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.internal.*
import java.util.concurrent.*
import kotlin.coroutines.*

/**
 * This [CoroutineContext] dispatcher can be used to simulate virtual time to speed up
 * code, especially tests, that deal with delays and timeouts in Coroutines.
 *
 * Provide an instance of this TestCoroutineContext when calling the *non-blocking*
 * [launch][CoroutineScope.launch] or [async][CoroutineScope.async]
 * and then advance time or trigger the actions to make the co-routines execute as soon as possible.
 *
 * This works much like the *TestScheduler* in RxJava2, which allows to speed up tests that deal
 * with non-blocking Rx chains that contain delays, timeouts, intervals and such.
 *
 * This dispatcher can also handle *blocking* coroutines that are started by [runBlocking].
 * This dispatcher's virtual time will be automatically advanced based on the delayed actions
 * within the Coroutine(s).
 *
 * **Note: This API will become obsolete in future updates due to integration with structured concurrency.**
 *           See [issue #541](https://github.com/Kotlin/kotlinx.coroutines/issues/541).
 *
 * @param name A user-readable name for debugging purposes.
 */
@Deprecated("This API has been deprecated to integrate with Structured Concurrency.",
        ReplaceWith("TestCoroutineScope", "kotlin.coroutines.test"),
        level = DeprecationLevel.WARNING)
class TestCoroutineContext(private val name: String? = null) : CoroutineContext {
    private val uncaughtExceptions = mutableListOf<Throwable>()

    private val ctxDispatcher = Dispatcher()

    private val ctxHandler = CoroutineExceptionHandler { _, exception ->
        uncaughtExceptions += exception
    }

    // The ordered queue for the runnable tasks.
    private val queue = ThreadSafeHeap<TimedRunnableObsolete>()

    // The per-scheduler global order counter.
    private var counter = 0L

    // Storing time in nanoseconds internally.
    private var time = 0L

    /**
     * Exceptions that were caught during a [launch][CoroutineScope.launch] or a [async][CoroutineScope.async] + [Deferred.await].
     */
    public val exceptions: List<Throwable> get() = uncaughtExceptions

    // -- CoroutineContext implementation 

    public override fun <R> fold(initial: R, operation: (R, CoroutineContext.Element) -> R): R =
        operation(operation(initial, ctxDispatcher), ctxHandler)

    @Suppress("UNCHECKED_CAST")
    public override fun <E : CoroutineContext.Element> get(key: CoroutineContext.Key<E>): E? = when {
        key === ContinuationInterceptor -> ctxDispatcher as E
        key === CoroutineExceptionHandler -> ctxHandler as E
        else -> null
    }

    public override fun minusKey(key: CoroutineContext.Key<*>): CoroutineContext = when {
        key === ContinuationInterceptor -> ctxHandler
        key === CoroutineExceptionHandler -> ctxDispatcher
        else -> this
    }

    /**
     * Returns the current virtual clock-time as it is known to this CoroutineContext.
     *
     * @param unit The [TimeUnit] in which the clock-time must be returned.
     * @return The virtual clock-time
     */
    public fun now(unit: TimeUnit = TimeUnit.MILLISECONDS)=
        unit.convert(time, TimeUnit.NANOSECONDS)

    /**
     * Moves the CoroutineContext's virtual clock forward by a specified amount of time.
     *
     * The returned delay-time can be larger than the specified delay-time if the code
     * under test contains *blocking* Coroutines.
     *
     * @param delayTime The amount of time to move the CoroutineContext's clock forward.
     * @param unit The [TimeUnit] in which [delayTime] and the return value is expressed.
     * @return The amount of delay-time that this CoroutineContext's clock has been forwarded.
     */
    public fun advanceTimeBy(delayTime: Long, unit: TimeUnit = TimeUnit.MILLISECONDS): Long {
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
    fun advanceTimeTo(targetTime: Long, unit: TimeUnit = TimeUnit.MILLISECONDS) {
        val nanoTime = unit.toNanos(targetTime)
        triggerActions(nanoTime)
        if (nanoTime > time) time = nanoTime
    }

    /**
     * Triggers any actions that have not yet been triggered and that are scheduled to be triggered at or
     * before this CoroutineContext's present virtual clock-time.
     */
    public fun triggerActions() = triggerActions(time)

    /**
     * Cancels all not yet triggered actions. Be careful calling this, since it can seriously
     * mess with your coroutines work. This method should usually be called on tear-down of a
     * unit test.
     */
    public fun cancelAllActions() {
        // An 'is-empty' test is required to avoid a NullPointerException in the 'clear()' method
        if (!queue.isEmpty) queue.clear()
    }

    /**
     * This method does nothing if there is one unhandled exception that satisfies the given predicate.
     * Otherwise it throws an [AssertionError] with the given message.
     *
     * (this method will clear the list of unhandled exceptions)
     *
     * @param message Message of the [AssertionError]. Defaults to an empty String.
     * @param predicate The predicate that must be satisfied.
     */
    public fun assertUnhandledException(message: String = "", predicate: (Throwable) -> Boolean) {
        if (uncaughtExceptions.size != 1 || !predicate(uncaughtExceptions[0])) throw AssertionError(message)
        uncaughtExceptions.clear()
    }

    /**
     * This method does nothing if there are no unhandled exceptions or all of them satisfy the given predicate.
     * Otherwise it throws an [AssertionError] with the given message.
     *
     * (this method will clear the list of unhandled exceptions)
     *
     * @param message Message of the [AssertionError]. Defaults to an empty String.
     * @param predicate The predicate that must be satisfied.
     */
    public fun assertAllUnhandledExceptions(message: String = "", predicate: (Throwable) -> Boolean) {
        if (!uncaughtExceptions.all(predicate)) throw AssertionError(message)
        uncaughtExceptions.clear()
    }

    /**
     * This method does nothing if one or more unhandled exceptions satisfy the given predicate.
     * Otherwise it throws an [AssertionError] with the given message.
     *
     * (this method will clear the list of unhandled exceptions)
     *
     * @param message Message of the [AssertionError]. Defaults to an empty String.
     * @param predicate The predicate that must be satisfied.
     */
    public fun assertAnyUnhandledException(message: String = "", predicate: (Throwable) -> Boolean) {
        if (!uncaughtExceptions.any(predicate)) throw AssertionError(message)
        uncaughtExceptions.clear()
    }

    /**
     * This method does nothing if the list of unhandled exceptions satisfy the given predicate.
     * Otherwise it throws an [AssertionError] with the given message.
     *
     * (this method will clear the list of unhandled exceptions)
     *
     * @param message Message of the [AssertionError]. Defaults to an empty String.
     * @param predicate The predicate that must be satisfied.
     */
    public fun assertExceptions(message: String = "", predicate: (List<Throwable>) -> Boolean) {
        if (!predicate(uncaughtExceptions)) throw AssertionError(message)
        uncaughtExceptions.clear()
    }

    private fun enqueue(block: Runnable) =
        queue.addLast(TimedRunnableObsolete(block, counter++))

    private fun postDelayed(block: Runnable, delayTime: Long) =
        TimedRunnableObsolete(block, counter++, time + TimeUnit.MILLISECONDS.toNanos(delayTime))
            .also {
                queue.addLast(it)
            }

    private fun processNextEvent(): Long {
        val current = queue.peek()
        if (current != null) {
            // Automatically advance time for EventLoop callbacks
            triggerActions(current.time)
        }
        return if (queue.isEmpty) Long.MAX_VALUE else 0L
    }

    private fun triggerActions(targetTime: Long) {
        while (true) {
            val current = queue.removeFirstIf { it.time <= targetTime } ?: break
            // If the scheduled time is 0 (immediate) use current virtual time
            if (current.time != 0L) time = current.time
            current.run()
        }
    }

    public override fun toString(): String = name ?: "TestCoroutineContext@$hexAddress"

    private inner class Dispatcher : EventLoop(), Delay {
        init {
            incrementUseCount() // this event loop is never completed
        }

        override fun dispatch(context: CoroutineContext, block: Runnable) {
            this@TestCoroutineContext.enqueue(block)
        }

        // override runBlocking to process this event loop
        override fun shouldBeProcessedFromContext(): Boolean = true

        override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
            postDelayed(Runnable {
                with(continuation) { resumeUndispatched(Unit) }
            }, timeMillis)
        }

        override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
            val node = postDelayed(block, timeMillis)
            return object : DisposableHandle {
                override fun dispose() {
                    queue.remove(node)
                }
            }
        }

        override fun processNextEvent() = this@TestCoroutineContext.processNextEvent()

        public override fun toString(): String = "Dispatcher(${this@TestCoroutineContext})"
    }
}

private class TimedRunnableObsolete(
    private val run: Runnable,
    private val count: Long = 0,
    @JvmField internal val time: Long = 0
) : Comparable<TimedRunnableObsolete>, Runnable by run, ThreadSafeHeapNode {
    override var heap: ThreadSafeHeap<*>? = null
    override var index: Int = 0

    override fun run() = run.run()

    override fun compareTo(other: TimedRunnableObsolete) = if (time == other.time) {
        count.compareTo(other.count)
    } else {
        time.compareTo(other.time)
    }

    override fun toString() = "TimedRunnable(time=$time, run=$run)"
}

/**
 * Executes a block of code in which a unit-test can be written using the provided [TestCoroutineContext]. The provided
 * [TestCoroutineContext] is available in the [testBody] as the `this` receiver.
 *
 * The [testBody] is executed and an [AssertionError] is thrown if the list of unhandled exceptions is not empty and
 * contains any exception that is not a [CancellationException].
 *
 * If the [testBody] successfully executes one of the [TestCoroutineContext.assertAllUnhandledExceptions],
 * [TestCoroutineContext.assertAnyUnhandledException], [TestCoroutineContext.assertUnhandledException] or
 * [TestCoroutineContext.assertExceptions], the list of unhandled exceptions will have been cleared and this method will
 * not throw an [AssertionError].
 *
 * **Note: This API will become obsolete in future updates due to integration with structured concurrency.**
 *           See [issue #541](https://github.com/Kotlin/kotlinx.coroutines/issues/541).
 *
 * @param testContext The provided [TestCoroutineContext]. If not specified, a default [TestCoroutineContext] will be
 * provided instead.
 * @param testBody The code of the unit-test.
 */
@Deprecated("This API has been deprecated to integrate with Structured Concurrency.",
        ReplaceWith("testContext.runBlockingTest(testBody)", "kotlin.coroutines.test"),
        level = DeprecationLevel.WARNING)
public fun withTestContext(testContext: TestCoroutineContext = TestCoroutineContext(), testBody: TestCoroutineContext.() -> Unit) {
    with (testContext) {
        testBody()
        if (!exceptions.all { it is CancellationException }) {
            throw AssertionError("Coroutine encountered unhandled exceptions:\n$exceptions")
        }
    }
}
