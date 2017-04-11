package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.CoroutineDispatcher
import kotlinx.coroutines.experimental.Delay
import kotlinx.coroutines.experimental.DisposableHandle
import kotlinx.coroutines.experimental.disposeOnCompletion
import reactor.core.Cancellation
import reactor.core.scheduler.Scheduler
import reactor.core.scheduler.TimedScheduler
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Converts an instance of [Scheduler] to an implementation of [CoroutineDispatcher].
 */
fun Scheduler.asCoroutineDispatcher() = SchedulerCoroutineDispatcher(this)

/**
 * Converts an instance of [TimedScheduler] to an implementation of [CoroutineDispatcher]
 * and provides native [delay][Delay.delay] support.
 */
fun TimedScheduler.asCoroutineDispatcher() = TimedSchedulerCoroutineDispatcher(this)

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary [Scheduler].
 * @param scheduler a scheduler.
 */
open class SchedulerCoroutineDispatcher(private val scheduler: Scheduler) : CoroutineDispatcher() {
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        scheduler.schedule(block)
    }

    override fun toString(): String = scheduler.toString()
    override fun equals(other: Any?): Boolean = other is SchedulerCoroutineDispatcher && other.scheduler === scheduler
    override fun hashCode(): Int = System.identityHashCode(scheduler)
}

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary [TimedScheduler].
 * @param scheduler a timed scheduler.
 */
open class TimedSchedulerCoroutineDispatcher(private val scheduler: TimedScheduler) : SchedulerCoroutineDispatcher(scheduler), Delay {

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val disposable = scheduler.schedule({
            with(continuation) { resumeUndispatched(Unit) }
        }, time, unit)

        continuation.disposeOnCompletion(disposable.asDisposableHandle())
    }

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle =
        scheduler.schedule(block, time, unit).asDisposableHandle()
}

private fun Cancellation.asDisposableHandle(): DisposableHandle =
        object : DisposableHandle {
            override fun dispose() = this@asDisposableHandle.dispose()
        }