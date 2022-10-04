/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("DEPRECATION")

package kotlinx.coroutines.test

import kotlinx.coroutines.*

/**
 * Control the virtual clock time of a [CoroutineDispatcher].
 *
 * Testing libraries may expose this interface to the tests instead of [TestCoroutineDispatcher].
 *
 * This interface is deprecated without replacement.
 * Instead, [TestCoroutineScheduler] is supposed to be used to control the virtual time.
 * Please see the
 * [migration guide](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-test/MIGRATION.md)
 * for an instruction on how to update the code for the new API.
 */
@ExperimentalCoroutinesApi
@Deprecated(
    "Use `TestCoroutineScheduler` to control virtual time.",
    level = DeprecationLevel.WARNING
)
// Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
public interface DelayController {
    /**
     * Returns the current virtual clock-time as it is known to this Dispatcher.
     *
     * @return The virtual clock-time
     */
    @ExperimentalCoroutinesApi
    public val currentTime: Long

    /**
     * Moves the Dispatcher's virtual clock forward by a specified amount of time.
     *
     * The amount the clock is progressed may be larger than the requested `delayTimeMillis` if the code under test uses
     * blocking coroutines.
     *
     * The virtual clock time will advance once for each delay resumed until the next delay exceeds the requested
     * `delayTimeMills`. In the following test, the virtual time will progress by 2_000 then 1 to resume three different
     * calls to delay.
     *
     * ```
     * @Test
     * fun advanceTimeTest() = runBlockingTest {
     *     foo()
     *     advanceTimeBy(2_000)  // advanceTimeBy(2_000) will progress through the first two delays
     *     // virtual time is 2_000, next resume is at 2_001
     *     advanceTimeBy(2)      // progress through the last delay of 501 (note 500ms were already advanced)
     *     // virtual time is 2_0002
     * }
     *
     * fun CoroutineScope.foo() {
     *     launch {
     *         delay(1_000)    // advanceTimeBy(2_000) will progress through this delay (resume @ virtual time 1_000)
     *         // virtual time is 1_000
     *         delay(500)      // advanceTimeBy(2_000) will progress through this delay (resume @ virtual time 1_500)
     *         // virtual time is 1_500
     *         delay(501)      // advanceTimeBy(2_000) will not progress through this delay (resume @ virtual time 2_001)
     *         // virtual time is 2_001
     *     }
     * }
     * ```
     *
     * @param delayTimeMillis The amount of time to move the CoroutineContext's clock forward.
     * @return The amount of delay-time that this Dispatcher's clock has been forwarded.
     */
    @ExperimentalCoroutinesApi
    public fun advanceTimeBy(delayTimeMillis: Long): Long

    /**
     * Immediately execute all pending tasks and advance the virtual clock-time to the last delay.
     *
     * If new tasks are scheduled due to advancing virtual time, they will be executed before `advanceUntilIdle`
     * returns.
     *
     * @return the amount of delay-time that this Dispatcher's clock has been forwarded in milliseconds.
     */
    @ExperimentalCoroutinesApi
    public fun advanceUntilIdle(): Long

    /**
     * Run any tasks that are pending at or before the current virtual clock-time.
     *
     * Calling this function will never advance the clock.
     */
    @ExperimentalCoroutinesApi
    public fun runCurrent()

    /**
     * Call after test code completes to ensure that the dispatcher is properly cleaned up.
     *
     * @throws AssertionError if any pending tasks are active, however it will not throw for suspended
     * coroutines.
     */
    @ExperimentalCoroutinesApi
    @Throws(AssertionError::class)
    public fun cleanupTestCoroutines()

    /**
     * Run a block of code in a paused dispatcher.
     *
     * By pausing the dispatcher any new coroutines will not execute immediately. After block executes, the dispatcher
     * will resume auto-advancing.
     *
     * This is useful when testing functions that start a coroutine. By pausing the dispatcher assertions or
     * setup may be done between the time the coroutine is created and started.
     */
    @Deprecated(
        "Please use a dispatcher that is paused by default, like `StandardTestDispatcher`.",
        level = DeprecationLevel.WARNING
    )
    // Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
    public suspend fun pauseDispatcher(block: suspend () -> Unit)

    /**
     * Pause the dispatcher.
     *
     * When paused, the dispatcher will not execute any coroutines automatically, and you must call [runCurrent] or
     * [advanceTimeBy], or [advanceUntilIdle] to execute coroutines.
     */
    @Deprecated(
        "Please use a dispatcher that is paused by default, like `StandardTestDispatcher`.",
        level = DeprecationLevel.WARNING
    )
    // Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
    public fun pauseDispatcher()

    /**
     * Resume the dispatcher from a paused state.
     *
     * Resumed dispatchers will automatically progress through all coroutines scheduled at the current time. To advance
     * time and execute coroutines scheduled in the future use, one of [advanceTimeBy],
     * or [advanceUntilIdle].
     */
    @Deprecated(
        "Please use a dispatcher that is paused by default, like `StandardTestDispatcher`.",
        level = DeprecationLevel.WARNING
    )
    // Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
    public fun resumeDispatcher()
}

internal interface SchedulerAsDelayController : DelayController {
    val scheduler: TestCoroutineScheduler

    /** @suppress */
    @Deprecated(
        "This property delegates to the test scheduler, which may cause confusing behavior unless made explicit.",
        ReplaceWith("this.scheduler.currentTime"),
        level = DeprecationLevel.WARNING
    )
    // Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
    override val currentTime: Long
        get() = scheduler.currentTime


    /** @suppress */
    @Deprecated(
        "This function delegates to the test scheduler, which may cause confusing behavior unless made explicit.",
        ReplaceWith("this.scheduler.apply { advanceTimeBy(delayTimeMillis); runCurrent() }"),
        level = DeprecationLevel.WARNING
    )
    // Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
    override fun advanceTimeBy(delayTimeMillis: Long): Long {
        val oldTime = scheduler.currentTime
        scheduler.advanceTimeBy(delayTimeMillis)
        scheduler.runCurrent()
        return scheduler.currentTime - oldTime
    }

    /** @suppress */
    @Deprecated(
        "This function delegates to the test scheduler, which may cause confusing behavior unless made explicit.",
        ReplaceWith("this.scheduler.advanceUntilIdle()"),
        level = DeprecationLevel.WARNING
    )
    // Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
    override fun advanceUntilIdle(): Long {
        val oldTime = scheduler.currentTime
        scheduler.advanceUntilIdle()
        return scheduler.currentTime - oldTime
    }

    /** @suppress */
    @Deprecated(
        "This function delegates to the test scheduler, which may cause confusing behavior unless made explicit.",
        ReplaceWith("this.scheduler.runCurrent()"),
        level = DeprecationLevel.WARNING
    )
    // Since 1.6.0, ERROR in 1.7.0 and removed as experimental in 1.8.0
    override fun runCurrent(): Unit = scheduler.runCurrent()

    /** @suppress */
    @ExperimentalCoroutinesApi
    override fun cleanupTestCoroutines() {
        // process any pending cancellations or completions, but don't advance time
        scheduler.runCurrent()
        if (!scheduler.isIdle(strict = false)) {
            throw UncompletedCoroutinesError(
                "Unfinished coroutines during tear-down. Ensure all coroutines are" +
                    " completed or cancelled by your test."
            )
        }
    }
}
