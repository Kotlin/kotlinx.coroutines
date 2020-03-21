/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.util.concurrent.*


// TODO most of these fields will be moved to 'object ExperimentalDispatcher'

internal const val DEFAULT_SCHEDULER_NAME = "DefaultDispatcher"

// 100us as default
@JvmField
internal val WORK_STEALING_TIME_RESOLUTION_NS = systemProp(
    "kotlinx.coroutines.scheduler.resolution.ns", 100000L
)

@JvmField
internal val BLOCKING_DEFAULT_PARALLELISM = systemProp(
    "kotlinx.coroutines.scheduler.blocking.parallelism", 16
)

// NOTE: we coerce default to at least two threads to give us chances that multi-threading problems
// get reproduced even on a single-core machine, but support explicit setting of 1 thread scheduler if needed.
@JvmField
internal val CORE_POOL_SIZE = systemProp(
    "kotlinx.coroutines.scheduler.core.pool.size",
    AVAILABLE_PROCESSORS.coerceAtLeast(2), // !!! at least two here
    minValue = CoroutineScheduler.MIN_SUPPORTED_POOL_SIZE
)

@JvmField
internal val MAX_POOL_SIZE = systemProp(
    "kotlinx.coroutines.scheduler.max.pool.size",
    (AVAILABLE_PROCESSORS * 128).coerceIn(
        CORE_POOL_SIZE,
        CoroutineScheduler.MAX_SUPPORTED_POOL_SIZE
    ),
    maxValue = CoroutineScheduler.MAX_SUPPORTED_POOL_SIZE
)

@JvmField
internal val IDLE_WORKER_KEEP_ALIVE_NS = TimeUnit.SECONDS.toNanos(
    systemProp("kotlinx.coroutines.scheduler.keep.alive.sec", 60L)
)

@JvmField
internal var schedulerTimeSource: TimeSource = NanoTimeSource

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

internal object NonBlockingContext : TaskContext {
    override val taskMode: Int = TASK_NON_BLOCKING

    override fun afterTask() {
       // Nothing for non-blocking context
    }
}

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

internal abstract class TimeSource {
    abstract fun nanoTime(): Long
}

internal object NanoTimeSource : TimeSource() {
    override fun nanoTime() = System.nanoTime()
}
