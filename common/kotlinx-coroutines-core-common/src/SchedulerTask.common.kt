/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

internal expect abstract class SchedulerTask() : Runnable

internal expect interface SchedulerTaskContext

@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
internal expect val SchedulerTask.taskContext: SchedulerTaskContext

@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
internal expect inline fun SchedulerTaskContext.afterTask()
