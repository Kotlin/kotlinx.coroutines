/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.Runnable
import java.io.*
import java.util.concurrent.*

internal interface Scheduler : Executor, Closeable {
    fun dispatch(block: Runnable, context: TaskContext = NonBlockingContext, tailDispatch: Boolean = false)
    fun createTask(block: Runnable, context: TaskContext): Runnable
    fun shutdown(l: Long)
}