package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * [CoroutineDispatcher] that performs both immediate and lazy execution of coroutines in tests
 * and uses a [TestCoroutineScheduler] to control its virtual clock.
 *
 * By default, [TestCoroutineDispatcher] is immediate. That means any tasks scheduled to be run without delay are
 * immediately executed. If they were scheduled with a delay, the virtual clock-time must be advanced via one of the
 * methods on the dispatcher's [scheduler].
 *
 * When switched to lazy execution using [pauseDispatcher] any coroutines started via [launch] or [async] will
 * not execute until a call to [DelayController.runCurrent] or the virtual clock-time has been advanced via one of the
 * methods on [DelayController].
 *
 * @see DelayController
 */
@Deprecated("The execution order of `TestCoroutineDispatcher` can be confusing, and the mechanism of " +
    "pausing is typically misunderstood. Please use `StandardTestDispatcher` or `UnconfinedTestDispatcher` instead.",
    level = DeprecationLevel.WARNING)
// Since 1.6.0, kept as warning in 1.7.0, ERROR in 1.8.0 and removed as experimental in 1.9.0
public class TestCoroutineDispatcher(public override val scheduler: TestCoroutineScheduler = TestCoroutineScheduler()):
    TestDispatcher(), Delay, SchedulerAsDelayController
{
    private var dispatchImmediately = true
        set(value) {
            field = value
            if (value) {
                // there may already be tasks from setup code we need to run
                scheduler.advanceUntilIdle()
            }
        }

    /** @suppress */
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        checkSchedulerInContext(scheduler, context)
        if (dispatchImmediately) {
            scheduler.sendDispatchEvent(context)
            block.run()
        } else {
            post(block, context)
        }
    }

    /** @suppress */
    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        checkSchedulerInContext(scheduler, context)
        post(block, context)
    }

    /** @suppress */
    override fun toString(): String = "TestCoroutineDispatcher[scheduler=$scheduler]"

    private fun post(block: Runnable, context: CoroutineContext) =
        scheduler.registerEvent(this, 0, block, context) { false }

    /** @suppress */
    @Deprecated(
        "Please use a dispatcher that is paused by default, like `StandardTestDispatcher`.",
        level = DeprecationLevel.ERROR
    )
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
    @Deprecated(
        "Please use a dispatcher that is paused by default, like `StandardTestDispatcher`.",
        level = DeprecationLevel.ERROR
    )
    override fun pauseDispatcher() {
        dispatchImmediately = false
    }

    /** @suppress */
    @Deprecated(
        "Please use a dispatcher that is paused by default, like `StandardTestDispatcher`.",
        level = DeprecationLevel.ERROR
    )
    override fun resumeDispatcher() {
        dispatchImmediately = true
    }
}
