package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import java.io.Closeable
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Unstable API and subject to change.
 * Context marker which gives scheduler a hint that submitted jobs can be distributed among cores aggressively.
 * Usually it's useful for massive jobs submission produced by single coroutine, e.g. data intensive fork-join tasks
 * or fan-out notifications for a large number of listeners.
 */
object ForkedMarker : AbstractCoroutineContextElement(ForkedKey)

private object ForkedKey : CoroutineContext.Key<ForkedMarker>

class ExperimentalCoroutineDispatcher(threads: Int = Runtime.getRuntime().availableProcessors()) : CoroutineDispatcher(), Delay, Closeable {

    private val coroutineScheduler = CoroutineScheduler(threads)

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        coroutineScheduler.dispatch(block, context[ForkedKey] != null)
    }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) =
            DefaultExecutor.scheduleResumeAfterDelay(time, unit, continuation)

    override fun close() = coroutineScheduler.close()
}
