package kotlinx.coroutines.experimental.scheduling


internal typealias Task = TimedTask
internal typealias GlobalQueue = TaskQueue

// 100us as default
internal val WORK_STEALING_TIME_RESOLUTION_NS = readFromSystemProperties(
        "kotlinx.coroutines.scheduler.resolution.ns", 100000L)

internal val QUEUE_SIZE_OFFLOAD_THRESHOLD = readFromSystemProperties(
        "kotlinx.coroutines.scheduler.offload.threshold", 96L)

internal val BLOCKING_DEFAULT_PARALLELISM = readFromSystemProperties(
        "kotlinx.coroutines.scheduler.blocking.parallelism", 16L).toInt()

internal val MAX_POOL_SIZE = readFromSystemProperties(
    "kotlinx.coroutines.scheduler.max.pool.size", Runtime.getRuntime().availableProcessors() * 128L).toInt()

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

private fun readFromSystemProperties(propertyName: String, defaultValue: Long): Long {
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
