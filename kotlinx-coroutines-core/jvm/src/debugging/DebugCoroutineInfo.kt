/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debugging

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import kotlinx.coroutines.debug.internal.DebugCoroutineInfo
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*

@PublishedApi
internal class DebugCoroutineInfo(
    delegate: DebugCoroutineInfoImpl,
    public val context: CoroutineContext
) {
    /**
     * [Job] associated with a current coroutine or null.
     */
    public val job: Job? get() = context[Job]

    /**
     * Last observed state of the coroutine
     */
    public val state: String = delegate.state
    
    /**
     * Creation stacktrace of the coroutine.
     */
    public val creationStackTrace = delegate.creationStackTrace

    /**
     * Last observed stacktrace of the coroutine captured on its suspension or resumption point.
     * It means that for [running][State.RUNNING] coroutines resulting stacktrace is inaccurate and
     * reflects stacktrace of the resumption point, not the actual current stacktrace.
     */
    public val lastObservedStackTrace: List<StackTraceElement> = delegate.lastObservedStackTrace()

    /**
     * Last observed thread used by a running coroutine.
     * Used in the debugger as an activeThread field.
     */
    public val lastObservedThread: Thread? = delegate.lastObservedThread

    // TODO: enhanceStackTraceWithThreadDumpAsJson
}
