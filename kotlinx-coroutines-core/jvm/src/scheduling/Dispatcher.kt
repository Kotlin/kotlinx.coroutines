package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.util.concurrent.*
import kotlin.coroutines.*

// Instance of Dispatchers.Default
internal object DefaultScheduler : SchedulerCoroutineDispatcher(
    CORE_POOL_SIZE, MAX_POOL_SIZE,
    IDLE_WORKER_KEEP_ALIVE_NS, DEFAULT_SCHEDULER_NAME
) {

    override fun limitedParallelism(parallelism: Int, name: String?): CoroutineDispatcher {
        parallelism.checkParallelism()
        if (parallelism >= CORE_POOL_SIZE) {
            return namedOrThis(name)
        }
        return super.limitedParallelism(parallelism, name)
    }

    // Shuts down the dispatcher, used only by Dispatchers.shutdown()
    internal fun shutdown() {
        super.close()
    }

    // Overridden in case anyone writes (Dispatchers.Default as ExecutorCoroutineDispatcher).close()
    override fun close() {
        throw UnsupportedOperationException("Dispatchers.Default cannot be closed")
    }

    override fun toString(): String = "Dispatchers.Default"
}

// The unlimited instance of Dispatchers.IO that utilizes all the threads CoroutineScheduler provides
private object UnlimitedIoScheduler : CoroutineDispatcher() {

    @InternalCoroutinesApi
    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        DefaultScheduler.dispatchWithContext(block, BlockingContext, fair = true)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        DefaultScheduler.dispatchWithContext(block, BlockingContext, fair = false)
    }

    override fun limitedParallelism(parallelism: Int, name: String?): CoroutineDispatcher {
        parallelism.checkParallelism()
        if (parallelism >= MAX_POOL_SIZE) {
            return namedOrThis(name)
        }
        return super.limitedParallelism(parallelism, name)
    }

    // This name only leaks to user code as part of .limitedParallelism machinery
    override fun toString(): String {
        return "Dispatchers.IO"
    }
}

internal fun scheduleBackgroundIoTask(block: Runnable) {
    DefaultScheduler.dispatchWithContext(UntrackableTask(block), BlockingContext, fair = false)
}

// Dispatchers.IO
internal object DefaultIoScheduler : ExecutorCoroutineDispatcher(), Executor {

    private val default = UnlimitedIoScheduler.limitedParallelism(
        systemProp(
            IO_PARALLELISM_PROPERTY_NAME,
            64.coerceAtLeast(AVAILABLE_PROCESSORS)
        )
    )

    override val executor: Executor
        get() = this

    override fun execute(command: java.lang.Runnable) = dispatch(EmptyCoroutineContext, command)

    override fun limitedParallelism(parallelism: Int, name: String?): CoroutineDispatcher {
        // See documentation to Dispatchers.IO for the rationale
        return UnlimitedIoScheduler.limitedParallelism(parallelism, name)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        default.dispatch(context, block)
    }

    @InternalCoroutinesApi
    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        default.dispatchYield(context, block)
    }

    override fun close() {
        error("Cannot be invoked on Dispatchers.IO")
    }

    override fun toString(): String = "Dispatchers.IO"
}

// Instantiated in tests so we can test it in isolation
internal open class SchedulerCoroutineDispatcher(
    private val corePoolSize: Int = CORE_POOL_SIZE,
    private val maxPoolSize: Int = MAX_POOL_SIZE,
    private val idleWorkerKeepAliveNs: Long = IDLE_WORKER_KEEP_ALIVE_NS,
    private val schedulerName: String = "CoroutineScheduler",
) : ExecutorCoroutineDispatcher() {

    override val executor: Executor
        get() = coroutineScheduler

    // This is variable for test purposes, so that we can reinitialize from clean state
    private var coroutineScheduler = createScheduler()

    private fun createScheduler() =
        CoroutineScheduler(corePoolSize, maxPoolSize, idleWorkerKeepAliveNs, schedulerName)

    override fun dispatch(context: CoroutineContext, block: Runnable): Unit = coroutineScheduler.dispatch(block)

    override fun dispatchYield(context: CoroutineContext, block: Runnable): Unit {
        /*
         * 'dispatchYield' implementation is needed to address the scheduler's scheduling policy.
         * By default, the scheduler dispatches tasks in a semi-LIFO order, meaning that for the
         * task sequence [#1, #2, #3], the scheduling of task #4 will produce
         * [#4, #1, #2, #3], allocates new worker and makes #4 stealable after some time.
         * On a fast enough system, it means that `while (true) { yield() }` might obstruct the progress
         * of the system and potentially starve it.
         * To mitigate that, `dispatchYield` is a dedicated entry point that produces [#1, #2, #3, #4]
         */
        coroutineScheduler.dispatch(block, fair = true)
    }

    internal fun dispatchWithContext(block: Runnable, context: TaskContext, fair: Boolean) {
        coroutineScheduler.dispatch(block, context, fair = fair)
    }

    override fun close() {
        coroutineScheduler.close()
    }

    // fot tests only
    @Synchronized
    internal fun usePrivateScheduler() {
        coroutineScheduler.shutdown(1_000L)
        coroutineScheduler = createScheduler()
    }

    // for tests only
    @Synchronized
    internal fun shutdown(timeout: Long) {
        coroutineScheduler.shutdown(timeout)
    }

    // for tests only
    internal fun restore() = usePrivateScheduler() // recreate scheduler
}
