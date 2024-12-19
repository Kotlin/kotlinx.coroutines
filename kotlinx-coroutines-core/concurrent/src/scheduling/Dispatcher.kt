package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

// Instance of Dispatchers.Default
@PublishedApi
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

    override fun toString(): String = "Dispatchers.Default"
}

// The unlimited instance of Dispatchers.IO that utilizes all the threads CoroutineScheduler provides
private object UnlimitedIoScheduler : CoroutineDispatcher() {

    @InternalCoroutinesApi
    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        DefaultScheduler.dispatchWithContext(block, BlockingContext, true)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        DefaultScheduler.dispatchWithContext(block, BlockingContext, false)
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

// Dispatchers.IO
internal object DefaultIoScheduler : CoroutineDispatcher() {

    private val default = UnlimitedIoScheduler.limitedParallelism(
        ioParallelism()
    )

    fun execute(command: Runnable) = dispatch(EmptyCoroutineContext, command)

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

    override fun toString(): String = "Dispatchers.IO"
}

// Instantiated in tests so we can test it in isolation
internal open class SchedulerCoroutineDispatcher(
    private val corePoolSize: Int = CORE_POOL_SIZE,
    private val maxPoolSize: Int = MAX_POOL_SIZE,
    private val idleWorkerKeepAliveNs: Long = IDLE_WORKER_KEEP_ALIVE_NS,
    private val schedulerName: String = "CoroutineScheduler",
): CoroutineDispatcher() {

    // This is variable for test purposes, so that we can reinitialize from clean state
    var coroutineScheduler = createScheduler()
        private set

    private val lock = SynchronizedObject()

    private fun createScheduler() =
        CoroutineScheduler(corePoolSize, maxPoolSize, idleWorkerKeepAliveNs, schedulerName)

    override fun dispatch(context: CoroutineContext, block: Runnable): Unit = coroutineScheduler.dispatch(block)

    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
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
        coroutineScheduler.dispatch(block, context, fair)
    }

    // Shuts down the dispatcher, used only by Dispatchers.shutdown()
    fun close() {
        coroutineScheduler.close()
    }

    // fot tests only
    internal fun usePrivateScheduler() {
        synchronized(lock) {
            coroutineScheduler.shutdown(1_000L)
            coroutineScheduler = createScheduler()
        }
    }

    // for tests only
    internal fun shutdown(timeout: Long) {
        synchronized(lock) {
            coroutineScheduler.shutdown(timeout)
        }
    }

    // for tests only
    internal fun restore() = usePrivateScheduler() // recreate scheduler
}

internal class ObjectRef<T>(@JvmField var element: T? = null)
