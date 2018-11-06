/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

internal expect abstract class SchedulerTask() : Runnable

internal expect interface SchedulerTaskContext

internal expect val SchedulerTask.taskContext: SchedulerTaskContext

internal expect inline fun SchedulerTaskContext.afterTask()
