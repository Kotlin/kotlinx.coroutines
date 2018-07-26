/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import java.util.concurrent.locks.LockSupport

internal interface TimeSource {
    fun currentTimeMillis(): Long
    fun nanoTime(): Long
    fun trackTask(block: Runnable): Runnable
    fun unTrackTask()
    fun registerTimeLoopThread()
    fun unregisterTimeLoopThread()
    fun parkNanos(blocker: Any, nanos: Long) // should return immediately when nanos <= 0
    fun unpark(thread: Thread)
}

internal object DefaultTimeSource : TimeSource {
    override fun currentTimeMillis(): Long = System.currentTimeMillis()
    override fun nanoTime(): Long = System.nanoTime()
    override fun trackTask(block: Runnable): Runnable = block
    override fun unTrackTask() {}
    override fun registerTimeLoopThread() {}
    override fun unregisterTimeLoopThread() {}

    override fun parkNanos(blocker: Any, nanos: Long) {
        LockSupport.parkNanos(blocker, nanos)
    }

    override fun unpark(thread: Thread) {
        LockSupport.unpark(thread)
    }
}

internal var timeSource: TimeSource = DefaultTimeSource
