package kotlinx.coroutines.experimental.scheduling

import java.util.concurrent.*


internal typealias Task = TimedTask
internal typealias GlobalQueue = TaskQueue
// TODO most of these fields will be moved to 'object ExperimentalDispatcher'

// 100us as default
@JvmField
internal val WORK_STEALING_TIME_RESOLUTION_NS = readFromSystemProperties(
        "kotlinx.coroutines.scheduler.resolution.ns", 100000L)

@JvmField
internal val QUEUE_SIZE_OFFLOAD_THRESHOLD = readFromSystemProperties(
        "kotlinx.coroutines.scheduler.offload.threshold", 96L)

@JvmField
internal val BLOCKING_DEFAULT_PARALLELISM = readFromSystemProperties(
        "kotlinx.coroutines.scheduler.blocking.parallelism", 16)

@JvmField
internal val CORE_POOL_SIZE = readFromSystemProperties(
    "kotlinx.coroutines.scheduler.core.pool.size", Runtime.getRuntime().availableProcessors().coerceAtLeast(2))

@JvmField
internal val MAX_POOL_SIZE = readFromSystemProperties(
    "kotlinx.coroutines.scheduler.max.pool.size", Runtime.getRuntime().availableProcessors() * 128)

@JvmField
internal val IDLE_WORKER_KEEP_ALIVE_NS = TimeUnit.SECONDS.toNanos(readFromSystemProperties(
    "kotlinx.coroutines.scheduler.keep.alive.sec", 5L))

@JvmField
internal var schedulerTimeSource: TimeSource = NanoTimeSource

internal enum class TaskMode {
    // Marker indicating that task is CPU-bound and will not block
    NON_BLOCKING,
    // Marker indicating that task may potentially block, thus giving scheduler a hint that additional thread may be required
    PROBABLY_BLOCKING,
}

internal data class TimedTask(val task: Runnable, val submissionTime: Long, val mode: TaskMode)

internal abstract class TimeSource {
    abstract fun nanoTime(): Long
}

internal object NanoTimeSource : TimeSource() {
    override fun nanoTime() = System.nanoTime()
}

internal fun readFromSystemProperties(propertyName: String, defaultValue: Int): Int = readFromSystemProperties(propertyName, defaultValue.toLong()).toInt()

internal fun readFromSystemProperties(propertyName: String, defaultValue: Long): Long {
    val value = try {
        System.getProperty(propertyName)
    } catch (e: SecurityException) {
        null
    } ?: return defaultValue

    val parsed = value.toLongOrNull() ?: error("System property '$propertyName' has unrecognized value '$value'")
    if (parsed <= 0) {
        error("System property '$propertyName' should be positive, but is '$parsed'")
    }
    return parsed
}
