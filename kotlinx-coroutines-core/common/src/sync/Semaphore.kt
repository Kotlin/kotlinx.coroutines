package kotlinx.coroutines.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*
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
        val p = _availablePermits.getAndAdd(-permits)
        if (p > 0) return // permit acquired
        addToQueueAndSuspend()
    }

    override fun release(permits: Int) {
        require(permits > 0) { "The number of released permits must be greater than 0" }
        val p = incPermits(permits)
        if (p >= 0) return // no waiters
        repeat(permits) {
            resumeNextFromQueue()
        }
    }

    internal fun incPermits(delta: Int = 1) = permitsBalance.getAndUpdate { cur ->
        assert { delta >= 1 }
        check(cur + delta <= permits) { "The number of released permits cannot be greater than $permits" }
        cur + delta
    }

    private suspend fun tryToAddToQueue(permits: Int) = suspendAtomicCancellableCoroutine<Unit> sc@{ cont ->
        val last = this.tail
        val enqIdx = enqIdx.getAndIncrement()
        val segment = getSegment(last, enqIdx / SEGMENT_SIZE)
        val i = (enqIdx % SEGMENT_SIZE).toInt()
        if (segment === null || segment.get(i) === RESUMED || !segment.cas(i, null, cont)) {
            // already resumed
            cont.resume(Unit)
            return@sc
        }
        cont.invokeOnCancellation(CancelSemaphoreAcquisitionHandler(this, segment, i).asHandler)
    }

    @Suppress("UNCHECKED_CAST")
    internal fun resumeNextFromQueue() {
        try_again@while (true) {
            val first = this.head
            val deqIdx = deqIdx.getAndIncrement()
            val segment = getSegmentAndMoveHead(first, deqIdx / SEGMENT_SIZE) ?: continue@try_again
            val i = (deqIdx % SEGMENT_SIZE).toInt()
            val cont = segment.getAndSet(i, RESUMED)
            if (cont === null) return // just resumed
            if (cont === CANCELLED) continue@try_again
            (cont as CancellableContinuation<Unit>).resume(Unit)
            return
        }
    }
}

private class CancelSemaphoreAcquisitionHandler(
    private val semaphore: SemaphoreImpl,
    private val segment: SemaphoreSegment,
    private val index: Int
) : CancelHandler() {
    override fun invoke(cause: Throwable?) {
        val p = semaphore.incPermits()
        if (p >= 0) return
        if (segment.cancel(index)) return
        semaphore.resumeNextFromQueue()
    }

    override fun toString() = "CancelSemaphoreAcquisitionHandler[$semaphore, $segment, $index]"
}

private class SemaphoreSegment(id: Long, prev: SemaphoreSegment?): Segment<SemaphoreSegment>(id, prev) {
    val acquirers = atomicArrayOfNulls<Any?>(SEGMENT_SIZE)
    private val cancelledSlots = atomic(0)
    override val removed get() = cancelledSlots.value == SEGMENT_SIZE

    @Suppress("NOTHING_TO_INLINE")
    inline fun get(index: Int): Any? = acquirers[index].value

    @Suppress("NOTHING_TO_INLINE")
    inline fun cas(index: Int, expected: Any?, value: Any?): Boolean = acquirers[index].compareAndSet(expected, value)

    @Suppress("NOTHING_TO_INLINE")
    inline fun getAndSet(index: Int, value: Any?) = acquirers[index].getAndSet(value)

    // Cleans the acquirer slot located by the specified index
    // and removes this segment physically if all slots are cleaned.
    fun cancel(index: Int): Boolean {
        // Try to cancel the slot
        val cancelled = getAndSet(index, CANCELLED) !== RESUMED
        // Remove this segment if needed
        if (cancelledSlots.incrementAndGet() == SEGMENT_SIZE)
            remove()
        return cancelled
    }

    override fun toString() = "SemaphoreSegment[id=$id, hashCode=${hashCode()}]"
}

@SharedImmutable
private val RESUMED = Symbol("RESUMED")
@SharedImmutable
private val CANCELLED = Symbol("CANCELLED")
@SharedImmutable
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.semaphore.segmentSize", 16)