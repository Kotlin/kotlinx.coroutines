/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("UNUSED")

package kotlinx.coroutines.debug.internal

import java.io.Serializable
import kotlin.coroutines.*
import kotlinx.coroutines.*

/*
 * This class represents all the data required by IDEA debugger.
 * It is serializable in order to speedup JDWP interactions
 */
internal class DebuggerInfo(source: DebugCoroutineInfo) : Serializable {
    public val coroutineId: Long? = source.context[CoroutineId]?.id
    public val dispatcher: String? = source.context[ContinuationInterceptor].toString()
    public val name: String? = source.context[CoroutineName]?.name
    public val state: String = source.state
    public val lastObservedThreadState: String? = source.lastObservedThread?.state?.toString()
    public val lastObservedThreadName = source.lastObservedThread?.name
    public val lastObservedStackTrace: List<StackTraceElement> = source.lastObservedStackTrace()
    public val sequenceNumber: Long = source.sequenceNumber
}
