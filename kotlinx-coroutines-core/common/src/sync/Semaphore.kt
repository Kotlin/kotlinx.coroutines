/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.math.*
import kotlin.native.concurrent.SharedImmutable

/**
 * A counting semaphore for coroutines that logically maintains a number of available permits.
 * Each [acquire] takes a single permit or suspends until it is available.
 * Each [release] adds a permit, potentially releasing a suspended acquirer.
 * Semaphore is fair and maintains a FIFO order of acquirers.
 *
 * Semaphores are mostly used to limit the number of coroutines that have an access to particular resource.
 * Semaphore with `permits = 1` is essentially a [Mutex].
 **/
public interface Semaphore {
    /**
     * Returns the current number of permits available in this semaphore.
     */
    public val availablePermits: Int

    /**
     * Acquires a permit from this semaphore, suspending until one is available.
     * All suspending acquirers are processed in first-in-first-out (FIFO) order.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     *
     * *Cancellation of suspended semaphore acquisition is atomic* -- when this function
     * throws [CancellationException] it means that the semaphore was not acquired.
     *
     * Note, that this function does not check for cancellation when it does not suspend.
     * Use [CoroutineScope.isActive] or [CoroutineScope.ensureActive] to periodically
     * check for cancellation in tight loops if needed.
     *
     * Use [tryAcquire] to try acquire a permit of this semaphore without suspension.
     */
    public suspend fun acquire()

    /**
     * Tries to acquire a permit from this semaphore without suspension.
     *
     * @return `true` if a permit was acquired, `false` otherwise.
     */
    public fun tryAcquire(): Boolean

    /**
     * Releases a permit, returning it into this semaphore. Resumes the first
     * suspending acquirer if there is one at the point of invocation.
     * Throws [IllegalStateException] if the number of [release] invocations is greater than the number of preceding [acquire].
     */
    public fun release()
}

/**
 * Creates new [Semaphore] instance.
 * @param permits the number of permits available in this semaphore.
 * @param acquiredPermits the number of already acquired permits,
 *        should be between `0` and `permits` (inclusively).
 */
@Suppress("FunctionName")
public fun Semaphore(permits: Int, acquiredPermits: Int = 0): Semaphore = SemaphoreImpl(permits, acquiredPermits)

/**
 * Executes the given [action], acquiring a permit from this semaphore at the beginning
 * and releasing it after the [action] is completed.
 *
 * @return the return value of the [action].
 */
public suspend inline fun <T> Semaphore.withPermit(action: () -> T): T {
    acquire()
    try {
        return action()
    } finally {
        release()
    }
}

private class SemaphoreImpl(private val permits: Int, acquiredPermits: Int) : Semaphore {

    // The queue of waiting acquirers is essentially an infinite array based on the list of segments
    // (see `SemaphoreSegment`); each segment contains a fixed number of slots. To determine a slot for each enqueue
    // and dequeue operation, we increment the corresponding counter at the beginning of the operation
    // and use the value before the increment as a slot number. This way, each enqueue-dequeue pair
    // works with an individual cell.We use the corresponding segment pointer to find the required ones.
    private val head: AtomicRef<SemaphoreSegment>
    private val deqIdx = atomic(0L)
    private val tail: AtomicRef<SemaphoreSegment>
    private val enqIdx = atomic(0L)

    init {
        require(permits > 0) { "Semaphore should have at least 1 permit, but had $permits" }
        require(acquiredPermits in 0..permits) { "The number of acquired permits should be in 0..$permits" }
        val s = SemaphoreSegment(0, null, 2)
        head = atomic(s)
        tail = atomic(s)
    }

    /**
     * This counter indicates a number of available permits if it is non-negative,
     * or the size with minus sign otherwise. Note, that 32-bit counter is enough here
     * since the maximal number of available permits is [permits] which is [Int],
     * and the maximum number of waiting acquirers cannot be greater than 2^31 in any
     * real application.
     */
    private val _availablePermits = atomic(permits - acquiredPermits)
    override val availablePermits: Int get() = max(_availablePermits.value, 0)

    override fun tryAcquire(): Boolean {
        _availablePermits.loop { p ->
            if (p <= 0) return false
            if (_availablePermits.compareAndSet(p, p - 1)) return true
        }
    }

    override suspend fun acquire() {
        while (true) {
            val p = _availablePermits.getAndDecrement()
            if (p > 0) return // permit acquired
            if (addToQueueAndSuspend()) return
        }
    }

    override fun release() {
        while (true) {
            val p = _availablePermits.getAndUpdate { cur ->
                check(cur < permits) { "The number of released permits cannot be greater than $permits" }
                cur + 1
            }
            if (p >= 0) return
            if (tryResumeNextFromQueue()) return
        }
    }

    /**
     * Returns `false` if the received permit cannot be used and the calling operation should restart.
     */
    private suspend fun addToQueueAndSuspend() = suspendAtomicCancellableCoroutineReusable<Boolean> sc@{ cont ->
        val curTail = this.tail.value
        val enqIdx = enqIdx.getAndIncrement()
        val segment = this.tail.findSegmentAndMoveForward(id = enqIdx / SEGMENT_SIZE, startFrom = curTail,
            createNewSegment = ::createSegment).segment // cannot be closed
        val i = (enqIdx % SEGMENT_SIZE).toInt()
        if (segment.get(i) === PERMIT || !segment.cas(i, null, cont)) {
            // The permit is already in the queue, try to grab it
            cont.resume(segment.cas(i, PERMIT, TAKEN))
            return@sc
        }
        cont.invokeOnCancellation(CancelSemaphoreAcquisitionHandler(segment, i).asHandler)
    }

    @Suppress("UNCHECKED_CAST")
    private fun tryResumeNextFromQueue(): Boolean {
        val curHead = this.head.value
        val deqIdx = deqIdx.getAndIncrement()
        val id = deqIdx / SEGMENT_SIZE
        val segment = this.head.findSegmentAndMoveForward(id, startFrom = curHead,
            createNewSegment = ::createSegment).segment // cannot be closed
        segment.cleanPrev()
        if (segment.id > id) return false
        val i = (deqIdx % SEGMENT_SIZE).toInt()
        val cont = segment.getAndSet(i, PERMIT)
        if (cont === CANCELLED) return false
        if (cont === null) {
            // Wait until an opposite operation comes for a bounded time
            repeat(MAX_SPIN_CYCLES) {
                if (segment.get(i) === TAKEN) return true
            }
            // Try to break the slot in order not to wait
            return !segment.cas(i, PERMIT, BROKEN)
        }
        return (cont as CancellableContinuation<Boolean>).tryResume()
    }
}

private fun CancellableContinuation<Boolean>.tryResume(): Boolean {
    val token = tryResume(true) ?: return false
    completeResume(token)
    return true
}

private class CancelSemaphoreAcquisitionHandler(
    private val segment: SemaphoreSegment,
    private val index: Int
) : CancelHandler() {
    override fun invoke(cause: Throwable?) {
        segment.cancel(index)
    }

    override fun toString() = "CancelSemaphoreAcquisitionHandler[$segment, $index]"
}

private fun createSegment(id: Long, prev: SemaphoreSegment?) = SemaphoreSegment(id, prev, 0)

private class SemaphoreSegment(id: Long, prev: SemaphoreSegment?, pointers: Int) : Segment<SemaphoreSegment>(id, prev, pointers) {
    val acquirers = atomicArrayOfNulls<Any?>(SEGMENT_SIZE)
    override val maxSlots: Int get() = SEGMENT_SIZE

    @Suppress("NOTHING_TO_INLINE")
    inline fun get(index: Int): Any? = acquirers[index].value

    @Suppress("NOTHING_TO_INLINE")
    inline fun set(index: Int, value: Any?) {
        acquirers[index].value = value
    }

    @Suppress("NOTHING_TO_INLINE")
    inline fun cas(index: Int, expected: Any?, value: Any?): Boolean = acquirers[index].compareAndSet(expected, value)

    @Suppress("NOTHING_TO_INLINE")
    inline fun getAndSet(index: Int, value: Any?) = acquirers[index].getAndSet(value)

    // Cleans the acquirer slot located by the specified index
    // and removes this segment physically if all slots are cleaned.
    fun cancel(index: Int) {
        // Clean the slot
        set(index, CANCELLED)
        // Remove this segment if needed
        onSlotCleaned()
    }

    override fun toString() = "SemaphoreSegment[id=$id, hashCode=${hashCode()}]"
}
@SharedImmutable
private val MAX_SPIN_CYCLES = systemProp("kotlinx.coroutines.semaphore.maxSpinCycles", 100_000)
@SharedImmutable
private val PERMIT = Symbol("PERMIT")
@SharedImmutable
private val TAKEN = Symbol("TAKEN")
@SharedImmutable
private val BROKEN = Symbol("TAKEN")
@SharedImmutable
private val CANCELLED = Symbol("CANCELLED")
@SharedImmutable
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.semaphore.segmentSize", 16)
