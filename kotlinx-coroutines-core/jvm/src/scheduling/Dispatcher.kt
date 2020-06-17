/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.util.concurrent.*
import kotlin.coroutines.*

/**
 * Default instance of coroutine dispatcher.
 */
internal object DefaultScheduler : ExperimentalCoroutineDispatcher() {
    val IO: CoroutineDispatcher = LimitingDispatcher(
        this,
        systemProp(IO_PARALLELISM_PROPERTY_NAME, 64.coerceAtLeast(AVAILABLE_PROCESSORS)),
        "Dispatchers.IO",
        TASK_PROBABLY_BLOCKING
    )

    override fun close() {
        throw UnsupportedOperationException("$DEFAULT_DISPATCHER_NAME cannot be closed")
    }

    override fun toString(): String = DEFAULT_DISPATCHER_NAME

    @InternalCoroutinesApi
    @Suppress("UNUSED")
    public fun toDebugString(): String = super.toString()
}

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
// TODO make internal (and rename) after complete integration
@InternalCoroutinesApi
public open class ExperimentalCoroutineDispatcher(
    private val corePoolSize: Int,
    private val maxPoolSize: Int,
    private val idleWorkerKeepAliveNs: Long,
    private val schedulerName: String = "CoroutineScheduler"
) : ExecutorCoroutineDispatcher() {
    public constructor(
        corePoolSize: Int = CORE_POOL_SIZE,
        maxPoolSize: Int = MAX_POOL_SIZE,
        schedulerName: String = DEFAULT_SCHEDULER_NAME
    ) : this(corePoolSize, maxPoolSize, IDLE_WORKER_KEEP_ALIVE_NS, schedulerName)

    @Deprecated(message = "Binary compatibility for Ktor 1.0-beta", level = DeprecationLevel.HIDDEN)
    public constructor(
        corePoolSize: Int = CORE_POOL_SIZE,
        maxPoolSize: Int = MAX_POOL_SIZE
    ) : this(corePoolSize, maxPoolSize, IDLE_WORKER_KEEP_ALIVE_NS)

    override val executor: Executor
        get() = coroutineScheduler

    // This is variable for test purposes, so that we can reinitialize from clean state
    private var coroutineScheduler = createScheduler()

    override fun dispatch(context: CoroutineContext, block: Runnable): Unit =
        try {
            coroutineScheduler.dispatch(block)
        } catch (e: RejectedExecutionException) {
            DefaultExecutor.dispatch(context, block)
        }

    override fun dispatchYield(context: CoroutineContext, block: Runnable): Unit =
        try {
            coroutineScheduler.dispatch(block, tailDispatch = true)
        } catch (e: RejectedExecutionException) {
            DefaultExecutor.dispatchYield(context, block)
        }

    override fun close(): Unit = coroutineScheduler.close()

    override fun toString(): String {
        return "${super.toString()}[scheduler = $coroutineScheduler]"
    }

    /**
     * Creates a coroutine execution context with limited parallelism to execute tasks which may potentially block.
     * Resulting [CoroutineDispatcher] doesn't own any resources (its threads) and provides a view of the original [ExperimentalCoroutineDispatcher],
     * giving it additional hints to adjust its behaviour.
     *
     * @param parallelism parallelism level, indicating how many threads can execute tasks in the resulting dispatcher parallel.
     */
    public fun blocking(parallelism: Int = BLOCKING_DEFAULT_PARALLELISM): CoroutineDispatcher {
        require(parallelism > 0) { "Expected positive parallelism level, but have $parallelism" }
        return LimitingDispatcher(this, parallelism, null, TASK_PROBABLY_BLOCKING)
    }

    /**
     * Creates a coroutine execution context with limited parallelism to execute CPU-intensive tasks.
     * Resulting [CoroutineDispatcher] doesn't own any resources (its threads) and provides a view of the original [ExperimentalCoroutineDispatcher],
     * giving it additional hints to adjust its behaviour.
     *
     * @param parallelism parallelism level, indicating how many threads can execute tasks in the resulting dispatcher parallel.
     */
    public fun limited(parallelism: Int): CoroutineDispatcher {
        require(parallelism > 0) { "Expected positive parallelism level, but have $parallelism" }
        require(parallelism <= corePoolSize) { "Expected parallelism level lesser than core pool size ($corePoolSize), but have $parallelism" }
        return LimitingDispatcher(this, parallelism, null, TASK_NON_BLOCKING)
    }

    internal fun dispatchWithContext(block: Runnable, context: TaskContext, tailDispatch: Boolean) {
        try {
            coroutineScheduler.dispatch(block, context, tailDispatch)
        } catch (e: RejectedExecutionException) {
            // Context shouldn't be lost here to properly invoke before/after task
            DefaultExecutor.enqueue(coroutineScheduler.createTask(block, context))
        }
    }

    private fun createScheduler() = CoroutineScheduler(corePoolSize, maxPoolSize, idleWorkerKeepAliveNs, schedulerName)

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

private class LimitingDispatcher(
    private val dispatcher: ExperimentalCoroutineDispatcher,
    private val parallelism: Int,
    private val name: String?,
    override val taskMode: Int
) : ExecutorCoroutineDispatcher(), TaskContext, Executor {

    private val queue = ConcurrentLinkedQueue<Runnable>()
    private val inFlightTasks = atomic(0)

    override val executor: Executor
        get() = this

    override fun execute(command: Runnable) = dispatch(command, false)

    override fun close(): Unit = error("Close cannot be invoked on LimitingBlockingDispatcher")

    override fun dispatch(context: CoroutineContext, block: Runnable) = dispatch(block, false)

    private fun dispatch(block: Runnable, tailDispatch: Boolean) {
        var taskToSchedule = block
        while (true) {
            // Commit in-flight tasks slot
            val inFlight = inFlightTasks.incrementAndGet()

            // Fast path, if parallelism limit is not reached, dispatch task and return
            if (inFlight <= parallelism) {
                dispatcher.dispatchWithContext(taskToSchedule, this, tailDispatch)
                return
            }

            // Parallelism limit is reached, add task to the queue
            queue.add(taskToSchedule)

            /*
             * We're not actually scheduled anything, so rollback committed in-flight task slot:
             * If the amount of in-flight tasks is still above the limit, do nothing
             * If the amount of in-flight tasks is lesser than parallelism, then
             * it's a race with a thread which finished the task from the current context, we should resubmit the first task from the queue
             * to avoid starvation.
             *
             * Race example #1 (TN is N-th thread, R is current in-flight tasks number), execution is sequential:
             *
             * T1: submit task, start execution, R == 1
             * T2: commit slot for next task, R == 2
             * T1: finish T1, R == 1
             * T2: submit next task to local queue, decrement R, R == 0
             * Without retries, task from T2 will be stuck in the local queue
             */
            if (inFlightTasks.decrementAndGet() >= parallelism) {
                return
            }

            taskToSchedule = queue.poll() ?: return
        }
    }

    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        dispatch(block, tailDispatch = true)
    }

    override fun toString(): String {
        return name ?: "${super.toString()}[dispatcher = $dispatcher]"
    }

    /**
     * Tries to dispatch tasks which were blocked due to reaching parallelism limit if there is any.
     *
     * Implementation note: blocking tasks are scheduled in a fair manner (to local queue tail) to avoid
     * non-blocking continuations starvation.
     * E.g. for
     * ```
     * foo()
     * blocking()
     * bar()
     * ```
     * it's more profitable to execute bar at the end of `blocking` rather than pending blocking task
     */
    override fun afterTask() {
        var next = queue.poll()
        // If we have pending tasks in current blocking context, dispatch first
        if (next != null) {
            dispatcher.dispatchWithContext(next, this, true)
            return
        }
        inFlightTasks.decrementAndGet()

        /*
         * Re-poll again and try to submit task if it's required otherwise tasks may be stuck in the local queue.
         * Race example #2 (TN is N-th thread, R is current in-flight tasks number), execution is sequential:
         * T1: submit task, start execution, R == 1
         * T2: commit slot for next task, R == 2
         * T1: finish T1, poll queue (it's still empty), R == 2
         * T2: submit next task to the local queue, decrement R, R == 1
         * T1: decrement R, finish. R == 0
         *
         * The task from T2 is stuck is the local queue
         */
        next = queue.poll() ?: return
        dispatch(next, true)
    }
}
