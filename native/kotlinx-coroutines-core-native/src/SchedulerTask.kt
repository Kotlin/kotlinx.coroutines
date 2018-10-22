/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias SchedulerTask = Runnable

internal actual abstract class SchedulerTaskBase actual constructor() : SchedulerTask

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias SchedulerTaskContext = Unit

internal actual val SchedulerTask.taskContext: SchedulerTaskContext get() = kotlin.Unit

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun SchedulerTask.afterTask(taskContext: SchedulerTaskContext) {}
