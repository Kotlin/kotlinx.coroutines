package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.coroutines.*

internal open class SegmentQueueSynchronizer<S, T> {
    // The queue of waiting acquirers is essentially an infinite array based on the list of segments
    // (see `SemaphoreSegment`); each segment contains a fixed number of slots. To determine a slot for each enqueue
    // and dequeue operation, we increment the corresponding counter at the beginning of the operation
    // and use the value before the increment as a slot number. This way, each enqueue-dequeue pair
    // works with an individual cell.We use the corresponding segment pointer to find the required ones.
    private val head: AtomicRef<SegmentQueueSynchronizerSegment>
    private val deqIdx = atomic(0L)
    private val tail: AtomicRef<SegmentQueueSynchronizerSegment>
    private val enqIdx = atomic(0L)

    init {
        val s = SegmentQueueSynchronizerSegment(0, null, 2)
        head = atomic(s)
        tail = atomic(s)
    }

    @Suppress("UNCHECKED_CAST")
    suspend fun suspend(sync: S, onCancellation: (S) -> Unit): T = suspendAtomicCancellableCoroutineReusable sc@{ cont ->
        val tail = this.tail.value
        val enqIdx = this.enqIdx.getAndIncrement()
        val segment = this.tail.findSegmentAndMoveForward(id = enqIdx / SEGMENT_SIZE, startFrom = tail,
            createNewSegment = ::createSegment).run { segment } // cannot be closed
        val i = (enqIdx % SEGMENT_SIZE).toInt()
        val old = segment.getAndSet(i, cont)
        if (old === null) {
            // added to the waiting queue
            cont.invokeOnCancellation(SegmentQueueSynchronizerCancelHandler(sync, segment, i, onCancellation).asHandler)
        } else {
            // already resumed
            segment.set(i, null)
            cont.resume(old as T)
        }
    }

    fun resumeNextWaiter(value: T) {
        while (!tryResumeNextWaiterInternal(value, true)) { /* repeat again */ }
    }

    fun tryResumeNextWaiter(value: T): Boolean = tryResumeNextWaiterInternal(value, false)

    @Suppress("UNCHECKED_CAST")
    private fun tryResumeNextWaiterInternal(value: T, updateDeqIdxInAdvance: Boolean): Boolean {
        val head = this.head.value
        val deqIdx = this.deqIdx.getAndIncrement()
        val id = deqIdx / SEGMENT_SIZE
        val segment = this.head.findSegmentAndMoveForward(id, startFrom = head,
            createNewSegment = ::createSegment).run { segment } // cannot be closed
        segment.cleanPrev()
        if (segment.id > id) {
            if (updateDeqIdxInAdvance) this.deqIdx.updateIfLower(segment.id * SEGMENT_SIZE)
            return false
        }
        val i = (deqIdx % SEGMENT_SIZE).toInt()
        val cont = segment.getAndSet(i, value)
        if (cont === null) return true // just resumed
        if (cont === CANCELLED) return false
        segment.set(i, null)
        cont as CancellableContinuation<T>
        return cont.tryResumeAndComplete(value)
    }
}

private inline fun AtomicLong.updateIfLower(value: Long): Unit = loop { cur ->
    if (cur >= value || compareAndSet(cur, value)) return
}

internal class SegmentQueueSynchronizerCancelHandler<S>(
    private val sync: S,
    private val segment: SegmentQueueSynchronizerSegment,
    private val index: Int,
    private val action: (S) -> Unit
    ) : CancelHandler() {
    override fun invoke(cause: Throwable?) {
        segment.cancel(index)
        action(sync)
    }

    override fun toString() = "SegmentQueueSynchronizerCancelHandler[$sync, $segment, $index, $action]"
}

internal class SegmentQueueSynchronizerSegment(id: Long, prev: SegmentQueueSynchronizerSegment?, pointers: Int)
    : Segment<SegmentQueueSynchronizerSegment>(id, prev, pointers)
{
    val waiters = atomicArrayOfNulls<Any?>(SEGMENT_SIZE)
    override val maxSlots: Int get() = SEGMENT_SIZE

    @Suppress("NOTHING_TO_INLINE")
    inline fun get(index: Int): Any? = waiters[index].value

    @Suppress("NOTHING_TO_INLINE")
    inline fun set(index: Int, value: Any?) {
        waiters[index].value = value
    }

    @Suppress("NOTHING_TO_INLINE")
    inline fun getAndSet(index: Int, value: Any?) = waiters[index].getAndSet(value)

    // Cleans the acquirer slot located by the specified index
    // and removes this segment physically if all slots are cleaned.
    fun cancel(index: Int): Boolean {
        // Try to cancel the slot
        val cancelled = getAndSet(index, CANCELLED) === null
        // Remove this segment if needed
        onSlotCleaned()
        return cancelled
    }

    override fun toString() = "SemaphoreSegment[id=$id, hashCode=${hashCode()}]"
}

private fun createSegment(id: Long, prev: SegmentQueueSynchronizerSegment?) = SegmentQueueSynchronizerSegment(id, prev, 0)

@SharedImmutable
private val CANCELLED = Symbol("CANCELLED")
@SharedImmutable
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.semaphore.segmentSize", 16)