package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.util.concurrent.*


/**
 * The name of the default scheduler. The names of the worker threads of [Dispatchers.Default] have it as their prefix.
 */
@JvmField
internal val DEFAULT_SCHEDULER_NAME = systemProp(
    "kotlinx.coroutines.scheduler.default.name", "DefaultDispatcher"
)

// 100us as default
@JvmField
internal val WORK_STEALING_TIME_RESOLUTION_NS = systemProp(
    "kotlinx.coroutines.scheduler.resolution.ns", 100000L
)

/**
 * The maximum number of threads allocated for CPU-bound tasks at the default set of dispatchers.
 *
 * NOTE: we coerce default to at least two threads to give us chances that multi-threading problems
 * get reproduced even on a single-core machine, but support explicit setting of 1 thread scheduler if needed
 */
@JvmField
internal val CORE_POOL_SIZE = systemProp(
    "kotlinx.coroutines.scheduler.core.pool.size",
    AVAILABLE_PROCESSORS.coerceAtLeast(2),
    minValue = CoroutineScheduler.MIN_SUPPORTED_POOL_SIZE
)

/** The maximum number of threads allocated for blocking tasks at the default set of dispatchers. */
@JvmField
internal val MAX_POOL_SIZE = systemProp(
    "kotlinx.coroutines.scheduler.max.pool.size",
    CoroutineScheduler.MAX_SUPPORTED_POOL_SIZE,
    maxValue = CoroutineScheduler.MAX_SUPPORTED_POOL_SIZE
)

@JvmField
internal val IDLE_WORKER_KEEP_ALIVE_NS = TimeUnit.SECONDS.toNanos(
    systemProp("kotlinx.coroutines.scheduler.keep.alive.sec", 60L)
)

@JvmField
internal var schedulerTimeSource: SchedulerTimeSource = NanoTimeSource

/**
 * Concurrency context of a task.
 *
 * Currently, it only signifies whether the task is blocking or non-blocking.
 */
internal typealias TaskContext = Boolean

/**
 * This would be [TaskContext.toString] if [TaskContext] was a proper class.
 */
private fun taskContextString(taskContext: TaskContext): String = if (taskContext) "Blocking" else "Non-blocking"

internal const val NonBlockingContext: TaskContext = false

internal const val BlockingContext: TaskContext = true

/**
 * A scheduler task.
 */
internal abstract class Task(
    @JvmField var submissionTime: Long,
    @JvmField var taskContext: TaskContext
) : Runnable {
    internal constructor() : this(0, NonBlockingContext)
}

internal inline val Task.isBlocking get() = taskContext

internal fun Runnable.asTask(submissionTime: Long, taskContext: TaskContext): Task =
    TaskImpl(this, submissionTime, taskContext)

// Non-reusable Task implementation to wrap Runnable instances that do not otherwise implement task
private class TaskImpl(
    @JvmField val block: Runnable,
    submissionTime: Long,
    taskContext: TaskContext
) : Task(submissionTime, taskContext) {
    override fun run() {
        block.run()
    }

    override fun toString(): String =
        "Task[${block.classSimpleName}@${block.hexAddress}, $submissionTime, ${taskContextString(taskContext)}]"
}

// Open for tests
internal class GlobalQueue : LockFreeTaskQueue<Task>(singleConsumer = false)

// Was previously TimeSource, renamed due to KT-42625 and KT-23727
internal abstract class SchedulerTimeSource {
    abstract fun nanoTime(): Long
}

internal object NanoTimeSource : SchedulerTimeSource() {
    override fun nanoTime() = System.nanoTime()
}
