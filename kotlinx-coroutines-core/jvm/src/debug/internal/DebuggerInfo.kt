/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("UNUSED")

package kotlinx.coroutines.debug.internal

import java.io.Serializable
import kotlin.coroutines.*
import kotlinx.coroutines.*

/*
 * This class represents all the data required by IDEA debugger.
 * It is serializable in order to speedup JDWP interactions.
 * **DO NOT MAKE BINARY-INCOMPATIBLE CHANGES TO THIS CLASS**.
 */
@PublishedApi
internal class DebuggerInfo(source: DebugCoroutineInfoImpl, context: CoroutineContext) : Serializable {
    public val coroutineId: Long? = context[CoroutineId]?.id
    public val dispatcher: String? = context[ContinuationInterceptor]?.toString()
    public val name: String? = context[CoroutineName]?.name
    public val state: String = source.state
    public val lastObservedThreadState: String? = source.lastObservedThread?.state?.toString()
    public val lastObservedThreadName = source.lastObservedThread?.name
    public val lastObservedStackTrace: List<StackTraceElement> = source.lastObservedStackTrace()
    public val sequenceNumber: Long = source.sequenceNumber
}
