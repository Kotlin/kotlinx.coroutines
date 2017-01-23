package kotlinx.coroutines.experimental

import java.util.concurrent.Executors
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicInteger
import kotlin.concurrent.thread
import kotlin.coroutines.CoroutineContext

/**
 * Creates new coroutine execution context with the a single thread and built-in [yield] and [delay] support.
 * All continuations are dispatched immediately when invoked inside the thread of this context.
 * Resources of this pool (its thread) are reclaimed when job of this context is cancelled.
 * The specified [name] defines the name of the new thread.
 * An optional [parent] job may be specified upon creation.
 */
fun newSingleThreadContext(name: String, parent: Job? = null): CoroutineContext =
    newFixedThreadPoolContext(1, name, parent)

/**
 * Creates new coroutine execution context with the fixed-size thread-pool and built-in [yield] and [delay] support.
 * All continuations are dispatched immediately when invoked inside the threads of this context.
 * Resources of this pool (its threads) are reclaimed when job of this context is cancelled.
 * The specified [name] defines the names of the threads.
 * An optional [parent] job may be specified upon creation.
 */
fun newFixedThreadPoolContext(nThreads: Int, name: String, parent: Job? = null): CoroutineContext {
    require(nThreads >= 1) { "Expected at least one thread, but $nThreads specified" }
    val job = Job(parent)
    return job + ThreadPoolDispatcher(nThreads, name, job)
}

private val thisThreadContext = ThreadLocal<ThreadPoolDispatcher>()

private class ThreadPoolDispatcher(
        nThreads: Int,
        name: String,
        val job: Job
) : CoroutineDispatcher(), Yield, Delay {
    val threadNo = AtomicInteger()
    val executor: ScheduledExecutorService = Executors.newScheduledThreadPool(nThreads) { target ->
        thread(start = false, isDaemon = true,
                name = if (nThreads == 1) name else name + "-" + threadNo.incrementAndGet()) {
            thisThreadContext.set(this@ThreadPoolDispatcher)
            target.run()
        }
    }

    init {
        job.onCompletion { executor.shutdown() }
    }

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = thisThreadContext.get() != this

    override fun dispatch(context: CoroutineContext, block: Runnable) = executor.execute(block)

    override fun scheduleResume(continuation: CancellableContinuation<Unit>) {
        executor.scheduleResume(continuation)
    }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        executor.scheduleResumeAfterDelay(time, unit, continuation)
    }
}
