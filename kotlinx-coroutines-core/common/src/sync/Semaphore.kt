package kotlinx.coroutines.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.math.*

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
     * Acquires the given number of permits from this semaphore, suspending until ones are available.
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
     * Use [tryAcquire] to try acquire the given number of permits of this semaphore without suspension.
     *
     * @param permits the number of permits to acquire
     *
     * @throws [IllegalArgumentException] if [permits] is less than or equal to zero.
     */
    public suspend fun acquire(permits: Int = 1)

    /**
     * Tries to acquire the given number of permits from this semaphore without suspension.
     *
     * @param permits the number of permits to acquire
     * @return `true` if all permits were acquired, `false` otherwise.
     *
     * @throws [IllegalArgumentException] if [permits] is less than or equal to zero.
     */
    public fun tryAcquire(permits: Int = 1): Boolean

    /**
     * Releases the given number of permits, returning them into this semaphore. Resumes the first
     * suspending acquirer if there is one at the point of invocation and the requested number of permits is available.
     *
     * @param permits the number of permits to release
     *
     * @throws [IllegalArgumentException] if [permits] is less than or equal to zero.
     * @throws [IllegalStateException] if the number of [release] invocations is greater than the number of preceding [acquire].
     */
    public fun release(permits: Int = 1)
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

private class SemaphoreImpl(
    private val permits: Int, acquiredPermits: Int
) : Semaphore, SegmentQueue<SemaphoreSegment>() {
    init {
        require(permits > 0) { "Semaphore should have at least 1 permit, but had $permits" }
        require(acquiredPermits in 0..permits) { "The number of acquired permits should be in 0..$permits" }
    }

    override fun newSegment(id: Long, prev: SemaphoreSegment?) = SemaphoreSegment(id, prev)

    /**
     * This counter indicates a number of available permits if it is non-negative,
     * or the size with minus sign otherwise. Note, that 32-bit counter is enough here
     * since the maximal number of available permits is [permits] which is [Int],
     * and the maximum number of waiting acquirers cannot be greater than 2^31 in any
     * real application.
     */
    private val permitsBalance = atomic(permits - acquiredPermits)
    override val availablePermits: Int get() = max(permitsBalance.value, 0)

    // The queue of waiting acquirers is essentially an infinite array based on `SegmentQueue`;
    // each segment contains a fixed number of slots. To determine a slot for each enqueue
    // and dequeue operation, we increment the corresponding counter at the beginning of the operation
    // and use the value before the increment as a slot number. This way, each enqueue-dequeue pair
    // works with an individual cell.
    private val enqIdx = atomic(0L)
    private val deqIdx = atomic(0L)

    /**
     * The remaining permits from release operations, which could not be spent, because the next slot was not defined
     */
    internal val accumulator = atomic(0)

    override fun tryAcquire(permits: Int): Boolean {
        require(permits > 0) { "The number of acquired permits must be greater than 0" }
        permitsBalance.loop { p ->
            if (p < permits) return false
            if (permitsBalance.compareAndSet(p, p - permits)) return true
        }
    }

    override suspend fun acquire(permits: Int) {
        require(permits > 0) { "The number of acquired permits must be greater than 0" }
        val p = permitsBalance.getAndAdd(-permits)
        if (p >= permits) return // permits are acquired
        tryToAddToQueue(permits)
    }

    override fun release(permits: Int) {
        require(permits > 0) { "The number of released permits must be greater than 0" }
        val p = incPermits(permits)
        if (p >= 0) return // no waiters
        tryToResumeFromQueue(permits)
    }

    internal fun incPermits(delta: Int = 1) = permitsBalance.getAndUpdate { cur ->
        assert { delta >= 1 }
        check(cur + delta <= permits) { "The number of released permits cannot be greater than $permits" }
        cur + delta
    }

    private suspend fun tryToAddToQueue(permits: Int) = suspendAtomicCancellableCoroutine<Unit> sc@{ cont ->
        val last = this.tail
        val enqueueId = enqIdx.getAndIncrement()
        val segmentId = enqueueId / SEGMENT_SIZE
        val segment = getSegment(last, segmentId)
        if (segment == null) {
            // The segment is already removed
            // Probably, this is the unreachable case
            cont.resume(Unit)
        } else {
            val slotId = (enqueueId % SEGMENT_SIZE).toInt()
            val prevCont = segment.continuations[slotId].getAndSet(cont)
            // It is safe to set continuation, because this slot is not defined yet, so another threads can not use it
            assert { prevCont == null }
            val prevSlot = segment.slots[slotId].getAndSet(permits)
            // The assertion is true, cause [RESUMED] can be set up only after [SUSPENDED]
            // and [CANCELLED] can be set up only in the handler, which will be added next
            assert { prevSlot == null }
            cont.invokeOnCancellation(CancelSemaphoreAcquisitionHandler(this, segment, slotId, permits).asHandler)
        }
        // Help to resume slots, if accumulator has permits
        tryToResumeFromQueue(0)
    }

    internal fun tryToResumeFromQueue(permits: Int) {
        val accumulated = accumulator.getAndSet(0) // try to take possession of all the accumulated permits at the moment
        var remain = permits + accumulated
        if (remain == 0) {
            // The accumulator had not any permits or the another thread stole permits. Also this method called with zero permits.
            return
        }
        try_again@ while (true) {
            val first = this.head
            val dequeueId = deqIdx.value
            val segmentId = dequeueId / SEGMENT_SIZE
            val segment = getSegmentAndMoveHead(first, segmentId)
            if (segment == null) {
                // The segment is already removed
                // Try to help to increment [deqIdx] once, because multiple threads can increment the [deqIdx] in parallel otherwise
                deqIdx.compareAndSet(dequeueId, dequeueId + 1)
                continue@try_again
            }
            val slotId = (dequeueId % SEGMENT_SIZE).toInt()
            val slot = segment.slots[slotId].value
            if (slot == null) {
                // If the slot is not defined yet we can't spent permits for it, so return [remain] to [accumulator]
                accumulator.addAndGet(remain)
                return
            }
            if (slot == CANCELLED) {
                // The slot was cancelled in the another thread
                // Try to help to increment [deqIdx] once, because multiple threads can increment the [deqIdx] in parallel otherwise
                if (deqIdx.compareAndSet(dequeueId, dequeueId + 1)) {
                    removeSegmentIfNeeded(segment, dequeueId + 1)
                }
                continue@try_again
            }
            if (slot == RESUMED) {
                // The slot was updated in the another thread
                // The another thread was supposed to increment [deqIdx]
                continue@try_again
            }
            val diff = min(slot, remain) // How many permits we can spent for the slot at most
            val newSlot = slot - diff
            if (!segment.slots[slotId].compareAndSet(slot, newSlot)) {
                // The slot was updated in another thread, let's try again
                continue@try_again
            }
            // Here we successfully updated the slot
            remain -= diff // remove spent permits
            if (newSlot == RESUMED) {
                segment.continuations[slotId].value!!.resume(Unit)
                removeSegmentIfNeeded(segment, deqIdx.incrementAndGet())
            }
            if (remain == 0) {
                // We spent all available permits, so let's finish
                return
            }
            // We still have permits, so we continue to spent them
        }
    }

    /**
     * Remove the segment if needed. The method checks, that all segment's slots were processed
     *
     * @param segment the segment to validation
     * @param dequeueId the current dequeue operation ID
     */
    internal fun removeSegmentIfNeeded(segment: SemaphoreSegment, dequeueId: Long) {
        val slotId = (dequeueId % SEGMENT_SIZE).toInt()
        if (slotId == SEGMENT_SIZE) {
            segment.remove()
        }
    }

    override fun toString(): String {
        return "Semaphore=(balance=${permitsBalance.value}, accumulator=${accumulator.value})"
    }
}

/**
 *  Cleans the acquirer slot located by the specified index and removes this segment physically if all slots are cleaned.
 */
private class CancelSemaphoreAcquisitionHandler(
        private val semaphore: SemaphoreImpl,
        private val segment: SemaphoreSegment,
        private val slotId: Int,
        private val permits: Int
) : CancelHandler() {
    override fun invoke(cause: Throwable?) {
        // Don't wait and use [prevSlot] to handle permits, because it starts races with release (see StressTest)
        val p = semaphore.incPermits(permits)
        if (p >= 0) return
        // Copy [slotId] to local variable to prevent exception:
        // "Complex data flow is not allowed for calculation of an array element index at the point of loading the reference to this element."
        val temp = slotId
        val prevSlot = segment.slots[temp].getAndSet(CANCELLED)
        // The assertion is true, cause the slot has [SUSPENDED] state at least
        assert { prevSlot != null }

        // Remove this segment if needed
        if (segment.cancelledSlots.incrementAndGet() == SEGMENT_SIZE) {
            segment.remove()
        }
        if (prevSlot == RESUMED) {
            // The slot has already resumed, so return free permits to the semaphore
            semaphore.tryToResumeFromQueue(prevSlot)
        }
    }

    override fun toString() = "CancelSemaphoreAcquisitionHandler[$semaphore, $segment, $slotId]"
}

private class SemaphoreSegment(id: Long, prev: SemaphoreSegment?) : Segment<SemaphoreSegment>(id, prev) {
    val continuations = atomicArrayOfNulls<CancellableContinuation<Unit>>(SEGMENT_SIZE)
    /**
     * Each slot can contain one of following values:
     * 1. A number greater than zero. It is [SUSPENDED] state;
     * 2. Zero. It is [RESUMED] state;
     * 3. "-1". It is [CANCELLED] state;
     * 4. "null". The slot is not defined yet.
     */
    val slots = atomicArrayOfNulls<Int>(SEGMENT_SIZE)
    val cancelledSlots = atomic(0)
    override val removed get() = cancelledSlots.value == SEGMENT_SIZE

    override fun toString(): String {
        return "SemaphoreSegment(id=$id)"
    }
}

@SharedImmutable
private val RESUMED = 0
@SharedImmutable
private val CANCELLED = -1
@SharedImmutable
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.semaphore.segmentSize", 1)