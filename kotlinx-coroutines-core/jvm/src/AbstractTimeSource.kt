// Need InlineOnly for efficient bytecode on Android
@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER", "NOTHING_TO_INLINE")

package kotlinx.coroutines

import java.util.concurrent.locks.*
import kotlin.internal.InlineOnly

internal abstract class AbstractTimeSource {
    abstract fun currentTimeMillis(): Long
    abstract fun nanoTime(): Long
    abstract fun wrapTask(block: Runnable): Runnable
    abstract fun trackTask(obj: Any)
    abstract fun unTrackTask(obj: Any)
    abstract fun registerTimeLoopThread()
    abstract fun unregisterTimeLoopThread()
    abstract fun parkNanos(blocker: Any, nanos: Long) // should return immediately when nanos <= 0
    abstract fun unpark(thread: Thread)
}

internal class UntrackableTask(val block: Runnable) : Runnable {
    override fun run() {
        block.run()
    }

    override fun toString(): String = "UntrackableTask(block=$block)"
}

// For tests only
// @JvmField: Don't use JvmField here to enable R8 optimizations via "assumenosideeffects"
private var timeSource: AbstractTimeSource? = null

// TODO: without this, there's a compilation error. Why?
internal inline fun mockTimeSource(source: AbstractTimeSource?) {
    timeSource = source
}

/**
 * The current system time in milliseconds.
 *
 * This is only used for automatically-generated tests in place of [System.currentTimeMillis],
 * it is not used in production code.
 */
@InlineOnly
internal inline fun currentTimeMillis(): Long =
    timeSource?.currentTimeMillis() ?: System.currentTimeMillis()

/**
 * The reading from a high-precision monotonic clock used for measuring time intervals.
 * Logically equivalent to [kotlin.time.TimeSource.Monotonic.markNow].
 */
@InlineOnly
internal actual inline fun nanoTime(): Long =
    timeSource?.nanoTime() ?: System.nanoTime()

/**
 * Calls [trackTask] and returns a wrapped version of the given [block] that calls [unTrackTask] after it completes.
 * Is optimized to just returning [block] if [trackTask] and [unTrackTask] are no-ops.
 */
@InlineOnly
internal inline fun wrapTask(block: Runnable): Runnable =
    timeSource?.wrapTask(block) ?: block

/**
 * Increments the number of tasks not under our control.
 *
 * Virtual time source uses this to decide whether to jump to the moment of virtual time when the next sleeping thread
 * should wake up.
 * If there are some uncontrollable tasks, it will not jump to the moment of the next sleeping thread,
 * because the uncontrollable tasks may change the shared state in a way that affects the sleeping thread.
 *
 * If [obj] is an instance of [UntrackableTask], it will not be tracked.
 *
 * Example:
 *
 * ```
 * thread { // controlled thread
 *   while (true) {
 *     if (sharedState == 42) {
 *       break
 *     }
 *     Thread.sleep(1000)
 *   }
 * }
 *
 * thread { // uncontrolled thread
 *   sharedState = 42
 * }
 * ```
 *
 * If the second thread is not tracked, the first thread effectively enters a spin loop until the second thread
 * physically changes the shared state.
 *
 * Every call to [trackTask] must be accompanied by a call to [unTrackTask] with the same [obj],
 * but [unTrackTask] can be called even if the corresponding [trackTask] wasn't called.
 */
@InlineOnly
internal inline fun trackTask(obj: Any) {
    timeSource?.apply {
        // only check `obj` after the `null` check, to avoid this extra work outside tests
        if (obj is UntrackableTask) return
        trackTask(obj)
    }
}

/**
 * Marks the task [obj] as complete. If [obj] wasn't tracked, does nothing. See [trackTask] for more details.
 */
@InlineOnly
internal inline fun unTrackTask(obj: Any) {
    timeSource?.unTrackTask(obj)
}

/**
 * Increases the registered number of nested loops of the form
 * `while (nanoTime() < deadline) { parkNanos(deadline - nanoTime()) }` corresponding to the object [key]
 * and signals that the current thread is in such a loop.
 *
 * While at least one such loop is running, other threads are allowed to call [unpark] on the current thread
 * and wake it up. Before [registerTimeLoopThread] is called, [unpark] is not guaranteed to have any effect.
 */
@InlineOnly
internal inline fun registerTimeLoopThread() {
    timeSource?.registerTimeLoopThread()
}

/**
 * The opposite of [registerTimeLoopThread].
 */
@InlineOnly
internal inline fun unregisterTimeLoopThread() {
    timeSource?.unregisterTimeLoopThread()
}

/**
 * Waits for either the specified number of nanoseconds to pass or until [unpark] is called.
 */
@InlineOnly
internal inline fun parkNanos(blocker: Any, nanos: Long) {
    timeSource?.parkNanos(blocker, nanos) ?: LockSupport.parkNanos(blocker, nanos)
}

/**
 * Preliminarily unparks the specified thread that's currently parked in [parkNanos].
 * Can be called even before the thread is parked.
 */
@InlineOnly
internal inline fun unpark(thread: Thread) {
    timeSource?.unpark(thread) ?: LockSupport.unpark(thread)
}
