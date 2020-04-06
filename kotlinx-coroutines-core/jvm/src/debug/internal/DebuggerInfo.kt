/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("PropertyName", "NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.debug.internal

import java.io.Serializable
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*

internal class DebuggerInfo(source: DebugCoroutineInfo) : Serializable {
    public val name: String? = source.context[kotlinx.coroutines.CoroutineName]?.name
    public val state: String = source.state
    public val lastObservedThreadState = source.lastObservedThread?.state
    public val lastObservedThreadName = source.lastObservedThread?.name
    public val lastObservedStackTrace = source.lastObservedStackTrace()
    public val sequenceNumber = source.sequenceNumber
}
