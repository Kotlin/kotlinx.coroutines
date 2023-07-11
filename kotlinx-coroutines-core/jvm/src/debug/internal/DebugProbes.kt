/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines.debug.internal

import kotlin.coroutines.*

/*
 * This class is used by ByteBuddy from kotlinx-coroutines-debug as kotlin.coroutines.jvm.internal.DebugProbesKt replacement.
 * In theory, it should belong to kotlinx-coroutines-debug, but placing it here significantly simplifies the
 * Android AS debugger that does on-load DEX transformation
 */

// Stubs which are injected as coroutine probes. Require direct match of signatures
internal fun probeCoroutineResumed(frame: Continuation<*>) = DebugProbesImpl.probeCoroutineResumed(frame)

internal fun probeCoroutineSuspended(frame: Continuation<*>) = DebugProbesImpl.probeCoroutineSuspended(frame)
internal fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> =
    DebugProbesImpl.probeCoroutineCreated(completion)
