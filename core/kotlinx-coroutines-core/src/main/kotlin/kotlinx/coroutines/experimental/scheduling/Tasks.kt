package kotlinx.coroutines.experimental.scheduling

import java.util.*

internal typealias Task = TimedTask
internal typealias GlobalQueue = Queue<Task>

// 100us is default resolution
internal val WORK_STEALING_TIME_RESOLUTION_NS = readFromSystemProperties(
        "kotlinx.coroutines.scheduler.resolution.ns", 100000L, String::toLongOrNull)

internal val QUEUE_SIZE_OFFLOAD_THRESHOLD = readFromSystemProperties(
        "kotlinx.coroutines.scheduler.offload.threshold", 96L, String::toLongOrNull)

internal var schedulerTimeSource: TimeSource = NanoTimeSource

internal data class TimedTask(val submissionTime: Long, val task: Runnable)

internal abstract class TimeSource {
    abstract fun nanoTime(): Long
}

internal object NanoTimeSource : TimeSource() {
    override fun nanoTime() = System.nanoTime()
}

private fun <T> readFromSystemProperties(propertyName: String, defaultValue: T, parser: (String) -> T?): T {
    val value = try {
        System.getProperty(propertyName)
    } catch (e: SecurityException) {
        null
    } ?: return defaultValue

    val parsed = parser(value)
    return parsed ?: error("System property '$propertyName' has unrecognized value '$value'")
}
