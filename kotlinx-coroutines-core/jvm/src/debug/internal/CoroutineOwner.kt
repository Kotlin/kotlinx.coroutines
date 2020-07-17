/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.internal

import kotlin.coroutines.*

/*
 * This interface is directly used by IDEA debugger to recognize instrumented coroutine frames.
 * **DO NOT MAKE BINARY-INCOMPATIBLE CHANGES TO THIS CLASS**.
 */
@PublishedApi
internal interface CoroutineOwner<T> : Continuation<T> {
    public fun getCoroutineInfo(): DebugCoroutineInfo
    public fun getDebuggerInfo(): DebuggerInfo
}