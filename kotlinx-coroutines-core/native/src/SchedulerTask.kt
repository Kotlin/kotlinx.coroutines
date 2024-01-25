package kotlinx.coroutines

internal actual abstract class SchedulerTask : Runnable

internal actual interface SchedulerTaskContext { }

private object TaskContext: SchedulerTaskContext { }

internal actual val SchedulerTask.taskContext: SchedulerTaskContext get() = TaskContext

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun SchedulerTaskContext.afterTask() {}
