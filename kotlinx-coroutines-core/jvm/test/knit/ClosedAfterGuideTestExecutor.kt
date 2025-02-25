package kotlinx.coroutines // Trick to make guide tests use these declarations with executors that can be closed on our side implicitly

import kotlinx.coroutines.testing.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.*

internal fun newSingleThreadContext(name: String): ExecutorCoroutineDispatcher = ClosedAfterGuideTestDispatcher(1, name)

private class ClosedAfterGuideTestDispatcher(
    private val nThreads: Int,
    private val name: String
) : ExecutorCoroutineDispatcher() {
    private val threadNo = AtomicInteger()

    override val executor: Executor =
        Executors.newScheduledThreadPool(nThreads, object : ThreadFactory {
            override fun newThread(target: java.lang.Runnable): Thread {
                return PoolThread(
                    this@ClosedAfterGuideTestDispatcher,
                    target,
                    if (nThreads == 1) name else name + "-" + threadNo.incrementAndGet()
                )
            }
        })

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        executor.execute(wrapTask(block))
    }

    override fun close() {
        (executor as ExecutorService).shutdown()
    }

    override fun toString(): String = "ThreadPoolDispatcher[$nThreads, $name]"
}
