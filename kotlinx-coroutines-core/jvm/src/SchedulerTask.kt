/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.scheduling.*

// fixme replace the suppress with AllowDifferentMembersInActual once stdlib is updated to 1.9.20 https://github.com/Kotlin/kotlinx.coroutines/issues/3846
@Suppress("ACTUAL_CLASSIFIER_MUST_HAVE_THE_SAME_MEMBERS_AS_NON_FINAL_EXPECT_CLASSIFIER")
internal actual typealias SchedulerTask = Task

// fixme replace the suppress with AllowDifferentMembersInActual once stdlib is updated to 1.9.20 https://github.com/Kotlin/kotlinx.coroutines/issues/3846
@Suppress("ACTUAL_CLASSIFIER_MUST_HAVE_THE_SAME_MEMBERS_AS_NON_FINAL_EXPECT_CLASSIFIER")
internal actual typealias SchedulerTaskContext = TaskContext

@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
internal actual val SchedulerTask.taskContext: SchedulerTaskContext get() = taskContext

@Suppress("NOTHING_TO_INLINE", "EXTENSION_SHADOWED_BY_MEMBER")
internal actual inline fun SchedulerTaskContext.afterTask() =
    afterTask()
