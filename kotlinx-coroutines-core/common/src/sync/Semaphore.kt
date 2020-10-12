/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.contracts.*
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
     * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
     * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
     * This function releases the semaphore if it was already acquired by this function before the [CancellationException]
     * was thrown.
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
@OptIn(ExperimentalContracts::class)
public suspend inline fun <T> Semaphore.withPermit(action: () -> T): T {
    contract {
        callsInPlace(action, InvocationKind.EXACTLY_ONCE)
    }

    acquire()
    try {
        return action()
    } finally {
        release()
    }
}

private class SemaphoreImpl(private val permits: Int, acquiredPermits: Int) : Semaphore {
    /*
       The queue of waiting acquirers is essentially an infinite array based on the list of segments
       (see `SemaphoreSegment`); each segment contains a fixed number of slots. To determine a slot for each enqueue
       and dequeue operation, we increment the corresponding counter at the beginning of the operation
       and use the value before the increment as a slot number. This way, each enqueue-dequeue pair
       works with an individual cell. We use the corresponding segment pointers to find the required ones.

       Here is a state machine for cells. Note that only one `acquire` and at most one `release` operation
       can deal with each cell, and that `release` uses `getAndSet(PERMIT)` to perform transitions for performance reasons
       so that the state `PERMIT` represents different logical states.

         +------+ `acquire` suspends   +------+   `release` tries    +--------+                    // if `cont.tryResume(..)` succeeds, then
         | NULL | -------------------> | cont | -------------------> | PERMIT | (cont RETRIEVED)   // the corresponding `acquire` operation gets
         +------+                      +------+   to resume `cont`   +--------+                    // a permit and the `release` one completes.
            |                             |
            |                             | `acquire` request is cancelled and the continuation is
            | `release` comes             | replaced with a special `CANCEL` token to avoid memory leaks
            | to the slot before          V
            | `acquire` and puts    +-----------+   `release` has    +--------+
            | a permit into the     | CANCELLED | -----------------> | PERMIT | (RElEASE FAILED)
            | slot, waiting for     +-----------+        failed      +--------+
            | `acquire` after
            | that.
            |
            |           `acquire` gets   +-------+
            |        +-----------------> | TAKEN | (ELIMINATION HAPPENED)
            V        |    the permit     +-------+
        +--------+   |
        | PERMIT | -<
        +--------+  |
                    |  `release` has waited a bounded time,   +--------+
                    +---------------------------------------> | BROKEN | (BOTH RELEASE AND ACQUIRE FAILED)
                           but `acquire` has not come         +--------+
    */

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

    private val onCancellationRelease = { _: Throwable -> release() }

    override fun tryAcquire(): Boolean {
        _availablePermits.loop { p ->
            if (p <= 0) return false
            if (_availablePermits.compareAndSet(p, p - 1)) return true
        }
    }

    override suspend fun acquire() {
        val p = _availablePermits.getAndDecrement()
        if (p > 0) return // permit acquired
        // While it looks better when the following function is inlined,
        // it is important to make `suspend` function invocations in a way
        // so that the tail-call optimization can be applied.
        acquireSlowPath()
    }

    private suspend fun acquireSlowPath() = suspendCancellableCoroutineReusable<Unit> sc@ { cont ->
        while (true) {
            if (addAcquireToQueue(cont)) return@sc
            val p = _availablePermits.getAndDecrement()
            if (p > 0) { // permit acquired
                cont.resume(Unit)
                return@sc
            }
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
    private fun addAcquireToQueue(cont: CancellableContinuation<Unit>): Boolean {
        val curTail = this.tail.value
        val enqIdx = enqIdx.getAndIncrement()
        val segment = this.tail.findSegmentAndMoveForward(id = enqIdx / SEGMENT_SIZE, startFrom = curTail,
            createNewSegment = ::createSegment).segment // cannot be closed
        val i = (enqIdx % SEGMENT_SIZE).toInt()
        // the regular (fast) path -- if the cell is empty, try to install continuation
        if (segment.cas(i, null, cont)) { // installed continuation successfully
            cont.invokeOnCancellation(CancelSemaphoreAcquisitionHandler(segment, i).asHandler)
            return true
        }
        // On CAS failure -- the cell must be either PERMIT or BROKEN
        // If the cell already has PERMIT from tryResumeNextFromQueue, try to grab it
        if (segment.cas(i, PERMIT, TAKEN)) { // took permit thus eliminating acquire/release pair
            // The following resume must always succeed, since continuation was not published yet and we don't have
            // to pass onCancellationRelease handle, since the coroutine did not suspend yet and cannot be cancelled
            cont.resume(Unit)
            return true
        }
        assert { segment.get(i) === BROKEN } // it must be broken in this case, no other way around it
        return false // broken cell, need to retry on a different cell
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
        val cellState = segment.getAndSet(i, PERMIT) // set PERMIT and retrieve the prev cell state
        when {
            cellState === null -> {
                // Acquire has not touched this cell yet, wait until it comes for a bounded time
                // The cell state can only transition from PERMIT to TAKEN by addAcquireToQueue
                repeat(MAX_SPIN_CYCLES) {
                    if (segment.get(i) === TAKEN) return true
                }
                // Try to break the slot in order not to wait
                return !segment.cas(i, PERMIT, BROKEN)
            }
            cellState === CANCELLED -> return false // the acquire was already cancelled
            else -> return (cellState as CancellableContinuation<Unit>).tryResumeAcquire()
        }
    }

    private fun CancellableContinuation<Unit>.tryResumeAcquire(): Boolean {
        val token = tryResume(Unit, null, onCancellationRelease) ?: return false
        completeResume(token)
        return true
    }
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
private val MAX_SPIN_CYCLES = systemProp("kotlinx.coroutines.semaphore.maxSpinCycles", 100)
@SharedImmutable
private val PERMIT = Symbol("PERMIT")
@SharedImmutable
private val TAKEN = Symbol("TAKEN")
@SharedImmutable
private val BROKEN = Symbol("BROKEN")
@SharedImmutable
private val CANCELLED = Symbol("CANCELLED")
@SharedImmutable
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.semaphore.segmentSize", 16)
