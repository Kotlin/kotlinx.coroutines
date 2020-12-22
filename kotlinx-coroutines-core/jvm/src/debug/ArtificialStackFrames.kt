/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug

public class ArtificialStackFrames {
    public fun coroutineCreation(): StackTraceElement = Exception().stackTrace.toList()[0]
    public fun coroutineBoundary(): StackTraceElement = Exception().stackTrace.toList()[0]
}
