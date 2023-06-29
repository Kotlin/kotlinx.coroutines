/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

internal actual abstract class SchedulerTask : Runnable

internal actual interface SchedulerTaskContext { }

private object taskContext: SchedulerTaskContext { }

internal actual val SchedulerTask.taskContext: SchedulerTaskContext get() = taskContext

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun SchedulerTaskContext.afterTask() {}

