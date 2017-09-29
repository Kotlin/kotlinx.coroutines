/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import java.util.concurrent.locks.LockSupport

internal interface TimeSource {
    fun nanoTime(): Long
    fun trackTask(block: Runnable): Runnable
    fun unTrackTask()
    fun registerTimeLoopThread()
    fun unregisterTimeLoopThread()
    fun parkNanos(blocker: Any, nanos: Long) // should return immediately when nanos <= 0
    fun unpark(thread: Thread)
}

internal object DefaultTimeSource : TimeSource {
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
