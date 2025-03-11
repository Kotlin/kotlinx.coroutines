package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import reactor.core.Disposable
import reactor.core.scheduler.Scheduler
import java.util.concurrent.TimeUnit
import kotlin.coroutines.CoroutineContext
import kotlin.time.Duration

/**
 * Converts an instance of [Scheduler] to an implementation of [CoroutineDispatcher].
 */
public fun Scheduler.asCoroutineDispatcher(): SchedulerCoroutineDispatcher = SchedulerCoroutineDispatcher(this)

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary [Scheduler].
 * @param scheduler a scheduler.
 */
public class SchedulerCoroutineDispatcher(
    /**
     * Underlying scheduler of current [CoroutineDispatcher].
     */
    public val scheduler: Scheduler
) : CoroutineDispatcher(), Delay {
    /** @suppress */
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        scheduler.schedule(block)
    }

    /** @suppress */
    override fun scheduleResumeAfterDelay(time: Duration, continuation: CancellableContinuation<Unit>) {
        val disposable = scheduler.schedule({
            with(continuation) { resumeUndispatched(Unit) }
        }, time.inWholeNanoseconds, TimeUnit.NANOSECONDS)
        continuation.disposeOnCancellation(disposable.asDisposableHandle())
    }

    /** @suppress */
    override fun invokeOnTimeout(time: Duration, block: Runnable, context: CoroutineContext): DisposableHandle =
        scheduler.schedule(block, time.inWholeNanoseconds, TimeUnit.NANOSECONDS).asDisposableHandle()

    /** @suppress */
    override fun toString(): String = scheduler.toString()
    /** @suppress */
    override fun equals(other: Any?): Boolean = other is SchedulerCoroutineDispatcher && other.scheduler === scheduler
    /** @suppress */
    override fun hashCode(): Int = System.identityHashCode(scheduler)
}

private fun Disposable.asDisposableHandle(): DisposableHandle =
    DisposableHandle { this@asDisposableHandle.dispose() }
