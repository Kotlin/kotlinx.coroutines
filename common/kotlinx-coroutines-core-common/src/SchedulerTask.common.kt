/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

internal expect interface SchedulerTask : Runnable 

internal expect abstract class SchedulerTaskBase() : SchedulerTask

internal expect inline fun SchedulerTask.afterTask()
