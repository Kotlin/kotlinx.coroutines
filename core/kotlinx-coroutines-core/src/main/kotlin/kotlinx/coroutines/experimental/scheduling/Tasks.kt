package kotlinx.coroutines.experimental.scheduling

import java.util.*

internal typealias Task = TimedTask
internal typealias GlobalQueue = Queue<Task>

internal val WORK_STEALING_TIME_RESOLUTION = readFromSystemProperties(
        "kotlinx.coroutines.scheduler.resolution.us", 500L, String::toLongOrNull)

internal val FORKED_TASK_OFFLOAD_THRESHOLD = readFromSystemProperties(
        "kotlinx.coroutines.scheduler.fork.threshold", 64L, String::toLongOrNull)

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
