package kotlinx.coroutines

internal expect abstract class SchedulerTask internal constructor() : Runnable

internal expect interface SchedulerTaskContext

@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
internal expect val SchedulerTask.taskContext: SchedulerTaskContext

@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
internal expect inline fun SchedulerTaskContext.afterTask()
