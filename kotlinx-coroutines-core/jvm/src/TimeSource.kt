/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// Need InlineOnly for efficient bytecode on Android
@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER", "NOTHING_TO_INLINE")

package kotlinx.coroutines

import java.util.concurrent.locks.*
import kotlin.internal.InlineOnly

internal interface TimeSource {
    fun currentTimeMillis(): Long
    fun nanoTime(): Long
    fun wrapTask(block: Runnable): Runnable
    fun trackTask()
    fun unTrackTask()
    fun registerTimeLoopThread()
    fun unregisterTimeLoopThread()
    fun parkNanos(blocker: Any, nanos: Long) // should return immediately when nanos <= 0
    fun unpark(thread: Thread)
}

// For tests only
// @JvmField: Don't use JvmField here to enable R8 optimizations via "assumenosideeffects"
internal var timeSource: TimeSource? = null

@InlineOnly
internal inline fun currentTimeMillis(): Long =
    timeSource?.currentTimeMillis() ?: System.currentTimeMillis()

@InlineOnly
internal inline fun nanoTime(): Long =
    timeSource?.nanoTime() ?: System.nanoTime()

@InlineOnly
internal inline fun wrapTask(block: Runnable): Runnable =
    timeSource?.wrapTask(block) ?: block

@InlineOnly
internal inline fun trackTask() {
    timeSource?.trackTask()
}

@InlineOnly
internal inline fun unTrackTask() {
    timeSource?.unTrackTask()
}

@InlineOnly
internal inline fun registerTimeLoopThread() {
    timeSource?.registerTimeLoopThread()
}

@InlineOnly
internal inline fun unregisterTimeLoopThread() {
    timeSource?.unregisterTimeLoopThread()
}

@InlineOnly
internal inline fun parkNanos(blocker: Any, nanos: Long) {
    timeSource?.parkNanos(blocker, nanos) ?: LockSupport.parkNanos(blocker, nanos)
}

@InlineOnly
internal inline fun unpark(thread: Thread) {
    timeSource?.unpark(thread) ?: LockSupport.unpark(thread)
}
