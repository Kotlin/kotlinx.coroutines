package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.coroutines.*

internal open class SegmentQueueSynchronizer<S: SegmentQueueSynchronizer<S, T>, T> {
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

    suspend fun suspend(onCancellation: (S) -> Unit) = suspendAtomicCancellableCoroutineReusable<Unit> sc@{ cont ->
        val curTail = this.tail.value
        val enqIdx = enqIdx.getAndIncrement()
        val segment = this.tail.findSegmentAndMoveForward(id = enqIdx / SEGMENT_SIZE, startFrom = curTail,
            createNewSegment = ::createSegment).run { segment } // cannot be closed
        val i = (enqIdx % SEGMENT_SIZE).toInt()
        if (segment.get(i) === RESUMED || !segment.cas(i, null, cont)) {
            // already resumed
            cont.resume(Unit)
            return@sc
        }
        cont.invokeOnCancellation(SegmentQueueSynchronizerCancelHandler(this as S, segment, i, onCancellation).asHandler)
    }

    @Suppress("UNCHECKED_CAST")
    fun resumeNextWaiter(value: T) {
        try_again@ while (true) {
            val curHead = this.head.value
            val deqIdx = deqIdx.getAndIncrement()
            val id = deqIdx / SEGMENT_SIZE
            val segment = this.head.findSegmentAndMoveForward(id, startFrom = curHead,
                createNewSegment = ::createSegment).run { segment } // cannot be closed
            segment.cleanPrev()
            if (segment.id > id) {
                this.deqIdx.updateIfLower(segment.id * SEGMENT_SIZE)
                continue@try_again
            }
            val i = (deqIdx % SEGMENT_SIZE).toInt()
            val cont = segment.getAndSet(i, RESUMED)
            if (cont === null) return // just resumed
            if (cont === CANCELLED) continue@try_again
            (cont as CancellableContinuation<Unit>).resume(Unit)
            return
        }
    }
}

private inline fun AtomicLong.updateIfLower(value: Long): Unit = loop { cur ->
    if (cur >= value || compareAndSet(cur, value)) return
}

internal class SegmentQueueSynchronizerCancelHandler<S : SegmentQueueSynchronizer<S, T>, T>(
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
    val acquirers = atomicArrayOfNulls<Any?>(SEGMENT_SIZE)
    override val maxSlots: Int get() = SEGMENT_SIZE

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
        onSlotCleaned()
        return cancelled
    }

    override fun toString() = "SemaphoreSegment[id=$id, hashCode=${hashCode()}]"
}

private fun createSegment(id: Long, prev: SegmentQueueSynchronizerSegment?) = SegmentQueueSynchronizerSegment(id, prev, 0)

@SharedImmutable
private val RESUMED = Symbol("RESUMED")
@SharedImmutable
private val CANCELLED = Symbol("CANCELLED")
@SharedImmutable
private val SEGMENT_SIZE = systemProp("kotlinx.coroutines.semaphore.segmentSize", 16)