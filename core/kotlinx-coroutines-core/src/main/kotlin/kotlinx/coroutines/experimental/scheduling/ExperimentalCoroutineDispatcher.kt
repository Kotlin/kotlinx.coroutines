package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import java.io.Closeable
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.CoroutineContext


class ExperimentalCoroutineDispatcher(threads: Int = Runtime.getRuntime().availableProcessors()) : CoroutineDispatcher(), Delay, Closeable {

    private val coroutineScheduler = CoroutineScheduler(threads)

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        coroutineScheduler.dispatch(block)
    }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) =
            DefaultExecutor.scheduleResumeAfterDelay(time, unit, continuation)

    override fun close() = coroutineScheduler.close()
    override fun toString(): String {
        return "${super.toString()}[scheduler = $coroutineScheduler]"
    }

}
