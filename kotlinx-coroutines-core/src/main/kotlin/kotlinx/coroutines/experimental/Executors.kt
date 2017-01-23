package kotlinx.coroutines.experimental

import java.util.concurrent.Executor
import java.util.concurrent.ExecutorService
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.TimeUnit
import kotlin.coroutines.CoroutineContext

/**
 * Converts an instance of [Executor] to an implementation of [CoroutineDispatcher].
 */
public fun Executor.toCoroutineDispatcher(): CoroutineDispatcher =
    ExecutorCoroutineDispatcher(this)

internal open class ExecutorCoroutineDispatcher(val executor: Executor) : CoroutineDispatcher(), Delay {
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = true
    override fun dispatch(context: CoroutineContext, block: Runnable) = executor.execute(block)

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        (executor as? ScheduledExecutorService ?: scheduledExecutor).scheduleResumeAfterDelay(time, unit, continuation)
    }
}

internal fun ExecutorService.scheduleResume(cont: CancellableContinuation<Unit>) {
    val future = submit { cont.resume(Unit) }
    cont.cancelFutureOnCompletion(future)
}

internal fun ScheduledExecutorService.scheduleResumeAfterDelay(time: Long, unit: TimeUnit, cont: CancellableContinuation<Unit>) {
    val timeout = schedule({ cont.resume(Unit) }, time, unit)
    cont.cancelFutureOnCompletion(timeout)
}
