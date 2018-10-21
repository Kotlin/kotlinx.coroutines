/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.scheduling.*

internal actual typealias SchedulerTask = Task

internal actual abstract class SchedulerTaskBase actual constructor() : SchedulerTask {
    override var submissionTime: Long = 0
    override var taskContext: TaskContext = NonBlockingContext
}

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun SchedulerTask.afterTask() = taskContext.afterTask()
