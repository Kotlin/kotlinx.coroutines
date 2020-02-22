/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

internal actual abstract class SchedulerTask : Runnable

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias SchedulerTaskContext = Unit

internal actual val SchedulerTask.taskContext: SchedulerTaskContext get() = kotlin.Unit

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun SchedulerTaskContext.afterTask() {}
