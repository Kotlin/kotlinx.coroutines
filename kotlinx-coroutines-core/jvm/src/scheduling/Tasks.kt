/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

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
 * Marker indicating that task is CPU-bound and will not block
 */
internal const val TASK_NON_BLOCKING = 0

/**
 * Marker indicating that task may potentially block, thus giving scheduler a hint that additional thread may be required
 */
internal const val TASK_PROBABLY_BLOCKING = 1

internal interface TaskContext {
    val taskMode: Int // TASK_XXX
    fun afterTask()
}

private class TaskContextImpl(override val taskMode: Int): TaskContext {
    override fun afterTask() {
        // Nothing for non-blocking context
    }
}

@JvmField
internal val NonBlockingContext: TaskContext = TaskContextImpl(TASK_NON_BLOCKING)

@JvmField
internal val BlockingContext: TaskContext = TaskContextImpl(TASK_PROBABLY_BLOCKING)

internal abstract class Task(
    @JvmField var submissionTime: Long,
    @JvmField var taskContext: TaskContext
) : Runnable {
    constructor() : this(0, NonBlockingContext)
    inline val mode: Int get() = taskContext.taskMode // TASK_XXX
}

internal inline val Task.isBlocking get() = taskContext.taskMode == TASK_PROBABLY_BLOCKING

// Non-reusable Task implementation to wrap Runnable instances that do not otherwise implement task
internal class TaskImpl(
    @JvmField val block: Runnable,
    submissionTime: Long,
    taskContext: TaskContext
) : Task(submissionTime, taskContext) {
    override fun run() {
        try {
            block.run()
        } finally {
            taskContext.afterTask()
        }
    }

    override fun toString(): String =
        "Task[${block.classSimpleName}@${block.hexAddress}, $submissionTime, $taskContext]"
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
