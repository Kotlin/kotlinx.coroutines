/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.internal.*
import java.util.concurrent.*


// TODO most of these fields will be moved to 'object ExperimentalDispatcher'

internal const val DEFAULT_SCHEDULER_NAME = "DefaultDispatcher"

// 100us as default
@JvmField
internal val WORK_STEALING_TIME_RESOLUTION_NS = systemProp(
    "kotlinx.coroutines.scheduler.resolution.ns", 100000L
)

@JvmField
internal val QUEUE_SIZE_OFFLOAD_THRESHOLD = systemProp(
    "kotlinx.coroutines.scheduler.offload.threshold", 96, maxValue = BUFFER_CAPACITY
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
    systemProp("kotlinx.coroutines.scheduler.keep.alive.sec", 5L)
)

@JvmField
internal var schedulerTimeSource: TimeSource = NanoTimeSource

internal enum class TaskMode {

    /**
     * Marker indicating that task is CPU-bound and will not block
     */
    NON_BLOCKING,

    /**
     * Marker indicating that task may potentially block, thus giving scheduler a hint that additional thread may be required
     */
    PROBABLY_BLOCKING,
}

internal interface TaskContext {
    val taskMode: TaskMode
    fun afterTask()
}

internal object NonBlockingContext : TaskContext {
    override val taskMode: TaskMode = TaskMode.NON_BLOCKING

    override fun afterTask() {
       // Nothing for non-blocking context
    }
}

internal class Task(
    @JvmField val block: Runnable,
    @JvmField val submissionTime: Long,
    @JvmField val taskContext: TaskContext
) : Runnable, LockFreeMPMCQueueNode<Task>() {
    val mode: TaskMode get() = taskContext.taskMode
    
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
internal open class GlobalQueue : LockFreeMPMCQueue<Task>() {
    // Open for tests
    public open fun removeFirstBlockingModeOrNull(): Task? =
        removeFirstOrNullIf { it.mode == TaskMode.PROBABLY_BLOCKING }
}

internal abstract class TimeSource {
    abstract fun nanoTime(): Long
}

internal object NanoTimeSource : TimeSource() {
    override fun nanoTime() = System.nanoTime()
}
