/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.scheduling.*

internal actual typealias SchedulerTask = Task

internal actual typealias SchedulerTaskContext = TaskContext

@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
internal actual val SchedulerTask.taskContext: SchedulerTaskContext get() = taskContext

@Suppress("NOTHING_TO_INLINE", "EXTENSION_SHADOWED_BY_MEMBER")
internal actual inline fun SchedulerTaskContext.afterTask() =
    afterTask()
