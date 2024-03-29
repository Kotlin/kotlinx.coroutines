// Need InlineOnly for efficient bytecode on Android
@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER", "NOTHING_TO_INLINE")

package kotlinx.coroutines

import java.util.concurrent.locks.*
import kotlin.internal.InlineOnly

internal abstract class AbstractTimeSource {
    abstract fun currentTimeMillis(): Long
    abstract fun nanoTime(): Long
    abstract fun wrapTask(block: Runnable): Runnable
    abstract fun trackTask()
    abstract fun unTrackTask()
    abstract fun registerTimeLoopThread()
    abstract fun unregisterTimeLoopThread()
    abstract fun parkNanos(blocker: Any, nanos: Long) // should return immediately when nanos <= 0
    abstract fun unpark(thread: Thread)
}

// For tests only
// @JvmField: Don't use JvmField here to enable R8 optimizations via "assumenosideeffects"
private var timeSource: AbstractTimeSource? = null

// TODO: without this, there's a compilation error. Why?
internal inline fun mockTimeSource(source: AbstractTimeSource?) {
    timeSource = source
}

@InlineOnly
internal inline fun currentTimeMillis(): Long =
    timeSource?.currentTimeMillis() ?: System.currentTimeMillis()

@InlineOnly
internal actual inline fun nanoTime(): Long =
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
