package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * @suppress
 */
@Deprecated("The execution order of `TestCoroutineDispatcher` can be confusing, and the mechanism of " +
    "pausing is typically misunderstood. Please use `StandardTestDispatcher` or `UnconfinedTestDispatcher` instead.",
    level = DeprecationLevel.ERROR)
// Since 1.6.0, kept as warning in 1.7.0, ERROR in 1.9.0 and removed as experimental later
public class TestCoroutineDispatcher(public override val scheduler: TestCoroutineScheduler = TestCoroutineScheduler()):
    TestDispatcher(), Delay
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

    val currentTime: Long
        get() = scheduler.currentTime

    fun advanceUntilIdle(): Long {
        val oldTime = scheduler.currentTime
        scheduler.advanceUntilIdle()
        return scheduler.currentTime - oldTime
    }

    fun runCurrent(): Unit = scheduler.runCurrent()

    fun cleanupTestCoroutines() {
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
